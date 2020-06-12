#lang forge

sig HeapCell {} --unit of memory

one sig Prologue extends HeapCell{} --starting point to determine reachability of memory
one sig Epilogue extends HeapCell{} --ending point to determine reachability of memory

sig State { --represents the memory state at a particular time
  blocks: set HeapCell,
  sizes: set HeapCell -> Int,
  pointers: set HeapCell -> Int,
  allocated: set HeapCell -> Int,
  prologue: one Prologue,
  epilogue: one Epilogue,
  next: set HeapCell->HeapCell,
  prev: set HeapCell->HeapCell,
  heapSize: one Int --get current size (in terms of words) of the HeapCell (later assert that it is equal to sum of all blocks)
}

--MIGHT JUST DO TWO STATES: BEFORE AND AFTER, Decide which algorithm in testing
one sig StateA extends State {}
one sig StateB extends State {
    size: one Int,
    toRealloc: one HeapCell,
    fit: set HeapCell
}
one sig StateC extends State {}


-----VALIDITY PREDS-------

--memory can only be a HeapCell, Prologue, or Epilogue
pred abstractHeapCell {
  HeapCell = Prologue + HeapCell + Epilogue
}

--only these  states appear in the model, each pred will be a state A to B transition
pred abstractState {
  State = StateA + StateB + StateC
}

--set up blocks,prologue,epilogue
pred prologue_epilogue[s: State] {
    #s.blocks >= 2
    one s.prologue
    s.prologue in s.blocks
    s.prologue.(s.sizes) = sing[1]
    s.prologue.(s.pointers) = sing[0]
    s.prologue.(s.allocated) = sing[1]
    one s.epilogue
    s.epilogue in s.blocks
    s.epilogue.(s.sizes) = sing[1]
    s.epilogue.(s.allocated) = sing[1]
    not s.prologue = s.epilogue
}

pred blocks_valid[s: State] {
    all cell : s.blocks | {
        one cell.(s.sizes)
        one cell.(s.pointers)
        one cell.(s.allocated)
        sum[cell.(s.sizes)] > 0
        (cell.(s.allocated) = sing[1] or cell.(s.allocated) = sing[0])
    }
    all cell : HeapCell - s.blocks | {
        no cell.(s.sizes)
        no cell.(s.pointers)
        no cell.(s.allocated)
        no cell.(s.next)
        no (s.next).cell
        no cell.(s.prev)
        no (s.prev).cell
    }
}

pred next_prev[s: State] {
    no iden & s.prev
    no iden & s.next --prev and next are irreflexive
    no s.prologue.(s.prev)
    no s.epilogue.(s.next)
    all cell : s.blocks - s.epilogue | {
        one cell.(s.next)
        one (s.prev).cell --all cells except for epilogue have a next
    }
    all cell : s.blocks - s.prologue | {
        one (s.next).cell
        one cell.(s.prev) --all cells except for prologue have a previous
    }
    all cell : s.blocks - s.prologue - s.epilogue | {
        (s.prev).cell = cell.(s.next)
        cell.(s.prev) = (s.next).cell --establishes everything in next and prev, prev is constrained as opposite of next
    }
    
    all cell : s.blocks-s.prologue | {
        cell.(s.pointers) = sing[add[sum[cell.(s.prev).(s.sizes)], sum[cell.(s.prev).(s.pointers)]]]
        cell in s.prologue.^(s.next)
    }
}

pred max_heapSize[s: State] {
    s.heapSize = sing[7]
    all cell : s.blocks | {
        { sum c : cell.*(s.prev) | sum[c.(s.sizes)] }  <= sum[s.heapSize]
        { sum c : cell.^(s.prev) | sum[c.(s.sizes)] } < { sum c : cell.*(s.prev) | sum[c.(s.sizes)] }
    }
}

pred coalesced[s: State] {
    all cell: HeapCell | cell.(s.allocated) = sing[0] implies cell.(s.prev).(s.allocated) = sing[1] and cell.(s.next).(s.allocated) = sing[1]
}

-- constraints for a valid state, also serves as initial state
pred validState[s: State] {
    -- Fill me in!
    abstractHeapCell
    abstractState
    prologue_epilogue[s]
    blocks_valid[s]
    next_prev[s]
    max_heapSize[s]
    coalesced[s]
}

--run { validState[StateA]} for 4 HeapCell, 2 State, 5 Int

pred coalesce_both[curr: HeapCell, pre: HeapCell, nxt: HeapCell] {
    StateC.prologue = StateB.prologue
    StateC.epilogue = StateB.epilogue
    StateC.blocks = StateB.blocks - curr - nxt
    StateC.next = StateB.next - pre -> curr - curr -> nxt - nxt -> nxt.(StateB.next) + pre -> nxt.(StateB.next)
    StateC.prev = StateB.prev - curr -> pre - nxt -> curr - nxt.(StateB.next) -> nxt + nxt.(StateB.next) -> pre
    StateC.sizes = StateB.sizes - pre -> pre.(StateB.sizes) - curr -> curr.(StateB.sizes) - nxt -> nxt.(StateB.sizes) + pre -> sing[add[sum[pre.(StateB.sizes)], sum[curr.(StateB.sizes)], sum[nxt.(StateB.sizes)]]]
    StateC.pointers = StateB.pointers - curr -> curr.(StateB.pointers) - nxt -> nxt.(StateB.pointers)
    StateC.allocated = StateB.allocated - curr -> curr.(StateB.allocated) - nxt -> nxt.(StateB.allocated)
    StateC.heapSize = StateB.heapSize
}

pred coalesce_prev[curr: HeapCell, pre: HeapCell] {
    StateC.prologue = StateB.prologue
    StateC.epilogue = StateB.epilogue
    StateC.blocks = StateB.blocks - curr
    StateC.next = StateB.next - pre -> curr - curr -> curr.(StateB.next) + pre -> curr.(StateB.next)
    StateC.prev = StateB.prev - curr -> pre - curr.(StateB.next) -> curr + curr.(StateB.next) -> pre
    StateC.sizes = StateB.sizes - pre -> pre.(StateB.sizes) - curr -> curr.(StateB.sizes) + pre -> sing[add[sum[pre.(StateB.sizes)], sum[curr.(StateB.sizes)]]]
    StateC.pointers = StateB.pointers - curr -> curr.(StateB.pointers)
    StateC.allocated = StateB.allocated - curr -> curr.(StateB.allocated)
    StateC.heapSize = StateB.heapSize
}

pred coalesce_next[curr: HeapCell, nxt: HeapCell] {
    StateC.prologue = StateB.prologue
    StateC.epilogue = StateB.epilogue
    StateC.blocks = StateB.blocks - nxt
    StateC.next = StateB.next - curr -> nxt - nxt -> nxt.(StateB.next) + curr -> nxt.(StateB.next)
    StateC.prev = StateB.prev - nxt -> curr - nxt.(StateB.next) -> nxt + nxt.(StateB.next) -> curr
    StateC.sizes = StateB.sizes - curr -> curr.(StateB.sizes) - nxt -> nxt.(StateB.sizes) + curr -> sing[add[sum[curr.(StateB.sizes)], sum[nxt.(StateB.sizes)]]]
    StateC.pointers = StateB.pointers - nxt -> nxt.(StateB.pointers)
    StateC.allocated = StateB.allocated - nxt -> nxt.(StateB.allocated)
    StateC.heapSize = StateB.heapSize
}

--stateB to stateC transition
pred coalesce[curr: HeapCell] {
    -- Fill me in!
    curr.(StateB.allocated) = sing[0] and curr.(StateB.prev).(StateB.allocated) = sing[1] and curr.(StateB.next).(StateB.allocated) = sing[1] implies {
        StateC.prologue = StateB.prologue
        StateC.epilogue = StateB.epilogue
        StateC.blocks = StateB.blocks
        StateC.next = StateB.next
        StateC.prev = StateB.prev
        StateC.sizes = StateB.sizes
        StateC.pointers = StateB.pointers
        StateC.allocated = StateB.allocated 
        StateC.heapSize = StateB.heapSize
    }
    curr.(StateB.allocated) = sing[0] and curr.(StateB.prev).(StateB.allocated) = sing[0] and curr.(StateB.next).(StateB.allocated) = sing[0] implies {
        coalesce_both[curr, curr.(StateB.prev), curr.(StateB.next)] 
    }

    curr.(StateB.allocated) = sing[0] and curr.(StateB.prev).(StateB.allocated) = sing[0] and curr.(StateB.next).(StateB.allocated) = sing[1] implies {
        coalesce_prev[curr, curr.(StateB.prev)] 
    }
    
    curr.(StateB.allocated) = sing[0] and curr.(StateB.prev).(StateB.allocated) = sing[1] and curr.(StateB.next).(StateB.allocated) = sing[0] implies {
        coalesce_next[curr, curr.(StateB.next)] 
    }
}

pred free {
    --constraints from malloc
    --INDUCTIVE, unreachable StateB state from malloc (try to make a case for when there is not, maybe size blocks == 2, find case when just free block
    --Add these cases!!!!
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks
    StateB.next = StateA.next
    StateB.prev = StateA.prev
    StateB.sizes = StateA.sizes
    StateB.pointers = StateA.pointers
    StateB.allocated = StateA.allocated - StateB.toRealloc -> sing[1] + StateB.toRealloc -> sing[0]
    StateB.heapSize = StateA.heapSize
    coalesce[StateB.toRealloc]
}

pred malloc[newFree : HeapCell, oldFree : HeapCell] {
    --free cell chosen to realloc, malloc to oldFree
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks + newFree - oldFree
    StateB.toRealloc = oldFree.(StateA.prev) implies {
        StateB.next = StateA.next - oldFree -> oldFree.(StateA.next) - StateB.toRealloc -> oldFree + StateB.toRealloc -> oldFree.(StateA.next) - StateB.toRealloc -> oldFree - StateB.toRealloc.(StateA.prev) -> StateB.toRealloc + StateB.toRealloc.(StateA.prev) -> newFree + newFree -> StateB.toRealloc
    StateB.prev = StateA.prev - oldFree -> StateB.toRealloc - oldFree.(StateA.next) -> oldFree + oldFree.(StateA.next) -> StateB.toRealloc - StateB.toRealloc -> StateB.toRealloc.(StateA.prev) - StateB.toRealloc.(StateA.next) -> StateB.toRealloc + newFree -> StateB.toRealloc.(StateA.prev) + StateB.toRealloc -> newFree
}
    not StateB.toRealloc = oldFree.(StateA.prev) implies {
        StateB.next = StateA.next - oldFree -> oldFree.(StateA.next) - oldFree.(StateA.prev) -> oldFree + oldFree.(StateA.prev) -> StateB.toRealloc +    StateB.toRealloc -> oldFree.(StateA.next) - StateB.toRealloc -> StateB.toRealloc.(StateA.next) - StateB.toRealloc.(StateA.prev) -> StateB.toRealloc + StateB.toRealloc.(StateA.prev) -> newFree + newFree -> StateB.toRealloc.(StateA.next)
    StateB.prev = StateA.prev - oldFree -> oldFree.(StateA.prev) - oldFree.(StateA.next) -> oldFree + oldFree.(StateA.next) -> StateB.toRealloc +    StateB.toRealloc -> oldFree.(StateA.prev) - StateB.toRealloc -> StateB.toRealloc.(StateA.prev) - StateB.toRealloc.(StateA.next) -> StateB.toRealloc + StateB.toRealloc.(StateA.next) -> newFree + newFree -> StateB.toRealloc.(StateA.prev)
}
    StateB.sizes = StateA.sizes - oldFree -> oldFree.(StateA.sizes) + newFree -> StateB.toRealloc.(StateA.sizes)
    StateB.pointers = StateA.pointers - oldFree -> oldFree.(StateA.pointers) + newFree -> StateB.toRealloc.(StateA.pointers) + StateB.toRealloc -> oldFree.(StateA.pointers)
    StateB.allocated = StateA.allocated - oldFree -> sing[0] + newFree -> sing[0]
    coalesce[newFree]
}

pred realloc_split[new : HeapCell, oldFree : HeapCell] {
    some newFree : HeapCell | {
        newFree not in StateA.blocks
        StateB.prologue = StateA.prologue
        StateB.epilogue = StateA.epilogue
        StateB.blocks = StateA.blocks + new + newFree - oldFree
        StateB.toRealloc = oldFree.(StateA.prev) implies {
        StateB.next = StateA.next - oldFree -> oldFree.(StateA.next) - StateB.toRealloc -> oldFree + StateB.toRealloc -> newFree + newFree -> oldFree.(StateA.next) - StateB.toRealloc -> oldFree - StateB.toRealloc.(StateA.prev) -> StateB.toRealloc + StateB.toRealloc.(StateA.prev) -> new + new -> StateB.toRealloc
    StateB.prev = StateA.prev - oldFree -> StateB.toRealloc - oldFree.(StateA.next) -> oldFree + oldFree.(StateA.next) -> newFree + newFree -> StateB.toRealloc - StateB.toRealloc -> StateB.toRealloc.(StateA.prev) - StateB.toRealloc.(StateA.next) -> StateB.toRealloc + new -> StateB.toRealloc.(StateA.prev) + StateB.toRealloc -> new
}
    not StateB.toRealloc = oldFree.(StateA.prev) implies {
        StateB.next = StateA.next - oldFree -> oldFree.(StateA.next) - oldFree.(StateA.prev) -> oldFree + oldFree.(StateA.prev) -> StateB.toRealloc +  StateB.toRealloc -> newFree + newFree -> oldFree.(StateA.next) - StateB.toRealloc -> StateB.toRealloc.(StateA.next) - StateB.toRealloc.(StateA.prev) -> StateB.toRealloc + StateB.toRealloc.(StateA.prev) -> new + new -> StateB.toRealloc.(StateA.next)
    StateB.prev = StateA.prev - oldFree -> oldFree.(StateA.prev) - oldFree.(StateA.next) -> oldFree + oldFree.(StateA.next) -> newFree + newFree -> StateB.toRealloc + StateB.toRealloc -> oldFree.(StateA.prev) - StateB.toRealloc -> StateB.toRealloc.(StateA.prev) - StateB.toRealloc.(StateA.next) -> StateB.toRealloc + StateB.toRealloc.(StateA.next) -> new + new -> StateB.toRealloc.(StateA.prev)
}
        StateB.sizes = StateA.sizes - oldFree -> oldFree.(StateA.sizes) + new -> StateB.toRealloc.(StateA.sizes) + newFree -> sing[subtract[sum[oldFree.(StateA.sizes)], sum[new.(StateB.sizes)]]] + StateB.toRealloc -> StateB.size - StateB.toRealloc -> StateB.toRealloc.(StateA.sizes)
        StateB.pointers = StateA.pointers - oldFree -> oldFree.(StateA.pointers) + new -> StateB.toRealloc.(StateA.pointers) + newFree -> sing[add[sum[new.(StateB.pointers)], sum[new.(StateB.sizes)]]] + StateB.toRealloc -> oldFree.(StateA.pointers)
        StateB.allocated = StateA.allocated - oldFree -> sing[0] + new -> sing[0] + newFree -> sing[0]
        coalesce[new]
        coalesce[newFree]
    }
}

pred addCellToEnd[newFree : HeapCell] {
    --free cell chosen to realloc, add to end
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks + newFree
    StateB.toRealloc = StateA.epilogue.(StateA.prev) implies {
        StateB.next = StateA.next - (StateB.toRealloc.(StateA.prev) -> StateB.toRealloc) + (StateB.toRealloc.(StateA.prev) -> newFree) + newFree -> StateB.toRealloc
        StateB.prev = StateA.prev - (StateB.toRealloc) -> StateB.toRealloc.(StateA.prev) + (newFree -> StateB.toRealloc.(StateA.prev)) + StateB.toRealloc -> newFree
        }
    not StateB.toRealloc = StateA.epilogue.(StateA.prev) implies {
    StateB.next = StateA.next - (StateA.epilogue.(StateA.prev) -> StateA.epilogue) + (StateA.epilogue.(StateA.prev) -> StateB.toRealloc) + (StateB.toRealloc -> StateB.epilogue) - (StateB.toRealloc.(StateA.prev) -> StateB.toRealloc) - (StateB.toRealloc -> StateB.toRealloc.(StateA.next)) + (StateB.toRealloc.(StateA.prev) -> newFree) + newFree -> StateB.toRealloc.(StateA.next)
    StateB.prev = StateA.prev - (StateA.epilogue.(StateA.next) -> StateA.epilogue) + (StateA.epilogue.(StateA.next) -> StateB.toRealloc) + (StateB.epilogue -> StateB.toRealloc) - (StateB.toRealloc.(StateA.prev) -> StateB.toRealloc) - (StateB.toRealloc -> StateB.toRealloc.(StateA.prev)) + (StateB.toRealloc.(StateA.next) -> newFree) + newFree -> StateB.toRealloc.(StateA.prev)
        }
    StateB.sizes = StateA.sizes + StateB.toRealloc -> StateB.size + newFree -> StateB.toRealloc.(StateA.sizes) - StateB.toRealloc -> StateB.toRealloc.(StateA.sizes)
    StateB.pointers = StateA.pointers - StateA.epilogue -> StateA.epilogue.(StateA.pointers) + StateB.toRealloc -> StateA.epilogue.(StateA.pointers) + StateB.epilogue -> sing[add[sum[StateA.epilogue.(StateA.pointers)], sum[StateB.size]]] - StateB.toRealloc -> StateB.toRealloc.(StateA.pointers) + newFree ->  StateB.toRealloc.(StateA.pointers)
    StateB.allocated = StateA.allocated + newFree -> sing[0]
    coalesce[newFree]
}

pred split {
    -- Fill me in!
    some newFree : HeapCell | {
        newFree not in StateA.blocks
        StateB.prologue = StateA.prologue
        StateB.epilogue = StateA.epilogue
        StateB.blocks = StateA.blocks + newFree
        StateB.next = StateA.next - StateB.toRealloc -> StateB.toRealloc.(StateA.next) + StateB.toRealloc -> newFree + newFree -> StateB.toRealloc.(StateA.next)
        StateB.prev = StateA.prev - StateB.toRealloc.(StateA.next) -> StateB.toRealloc + StateB.toRealloc.(StateA.next) -> newFree + newFree -> StateB.toRealloc 
        StateB.sizes = StateA.sizes - StateB.toRealloc -> StateB.toRealloc.(StateA.sizes) + StateB.toRealloc -> StateB.size + newFree -> sing[subtract[sum[StateB.toRealloc.(StateA.sizes)], sum[StateB.size]]]
        StateB.pointers = StateA.pointers + newFree -> sing[add[sum[StateB.toRealloc.(StateA.pointers)], sum[StateB.size]]]
        StateB.allocated = StateA.allocated + newFree -> sing[0]
        coalesce[newFree]
     }
}

--best-fit malloc, get free block and either malloc, add to end (sbrk), or split
pred best_fit_realloc {
    StateB.heapSize = StateA.heapSize
    StateC.heapSize = StateB.heapSize
    sum[StateB.size] >= 0
    all cell : HeapCell | StateB.toRealloc = cell iff cell in StateA.blocks and not cell = StateA.epilogue and not cell = StateA.prologue and cell.(StateA.allocated) = sing[1]
    all cell : StateB.blocks | {
        { sum c : cell.*(StateB.prev) | sum[c.(StateB.sizes)] }  <= sum[StateB.heapSize]
        { sum c : cell.^(StateB.prev) | sum[c.(StateB.sizes)] } < { sum c : cell.*(StateB.prev) | sum[c.(StateB.sizes)] }
    }
    all cell : HeapCell | cell in StateB.fit iff cell in StateA.blocks and cell.(StateA.allocated) = sing[0] and sum[cell.(StateA.sizes)] >= sum[StateB.size] --find blocks to fit if realloc is greater size than original
    sum[StateB.size] = 0 implies free
    sum[StateB.size] > 0 and sum[StateB.size] = sum[StateB.toRealloc.(StateA.sizes)] implies { --no change
        StateB.blocks = StateA.blocks
        StateB.sizes = StateA.sizes
        StateB.pointers = StateA.pointers
        StateB.allocated = StateA.allocated
        StateB.prologue = StateA.prologue
        StateB.epilogue = StateA.epilogue
        StateB.next = StateA.next
        StateB.prev = StateA.prev
        StateC.blocks = StateB.blocks
        StateC.sizes = StateB.sizes
        StateC.pointers = StateB.pointers
        StateC.allocated = StateB.allocated
        StateC.prologue = StateB.prologue
        StateC.epilogue = StateB.epilogue
        StateC.next = StateB.next
        StateC.prev = StateB.prev
    }
    sum[StateB.size] > 0 and sum[StateB.size] < sum[StateB.toRealloc.(StateA.sizes)] implies split
    sum[StateB.size] > 0 and sum[StateB.size] > sum[StateB.toRealloc.(StateA.sizes)] implies {
        some newCell : HeapCell | { --here, newCell is the cell that takes the place of the previously allocated cell (now free space)
            newCell not in StateA.blocks
            no StateB.fit implies addCellToEnd[newCell] 
            all best : StateB.fit | {
                sum[best.(StateA.sizes)] = min[StateB.fit.(StateA.sizes)] and min[StateB.fit.(StateA.sizes)] = sum[StateB.size] implies malloc[newCell, best]
                sum[best.(StateA.sizes)] = min[StateB.fit.(StateA.sizes)] and min[StateB.fit.(StateA.sizes)] > sum[StateB.size] implies realloc_split[newCell, best]
            }
        }
    }
}


--run { validState[StateA] and best_fit_realloc } for exactly 6 HeapCell, 3 State, 4 Int
--consistent: check { (validState[StateA] and best_fit_realloc) implies validState[StateB] } for 6 HeapCell, exactly 3 State, exactly 4 Int --should find counterexamples because not yet coalesced
--consistentCoalesce: check { (validState[StateA] and best_fit_realloc) implies validState[StateC] } for 4 HeapCell, exactly 3 State, exactly 4 Int


------------------------ TESTING SECTION ------------------------

inst boiler {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    heapSize = StateA0->sing[7] + StateB0->sing[7] + StateC0->sing[7] 
}

--Realloc size 0 has same beginning, middle, and end state
inst size_equal {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1 + HeapCell2 + HeapCell3 + HeapCell4
    blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->Epilogue0 + StateC0->Prologue0 + StateC0->HeapCell0 + StateC0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[3] + StateB0->Epilogue0->sing[1] + StateC0->Prologue0->sing[1] + StateC0->HeapCell0->sing[3] + StateC0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->Epilogue0->sing[1] + StateC0->Prologue0->sing[1] + StateC0->HeapCell0->sing[1] + StateC0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->Epilogue0->sing[4] + StateC0->Prologue0->sing[0] + StateC0->HeapCell0->sing[1] + StateC0->Epilogue0->sing[4]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateC0->HeapCell0->Prologue0 + StateC0->Epilogue0->HeapCell0
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->Epilogue0 + StateC0->Prologue0->HeapCell0 + StateC0->HeapCell0->Epilogue0
    size = StateB0->sing[3]
    toRealloc = StateB0->HeapCell0
    no fit
}

inst size_zero {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1 + HeapCell2 + HeapCell3 + HeapCell4
    blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->Epilogue0 + StateC0->Prologue0 + StateC0->HeapCell0 + StateC0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[3] + StateB0->Epilogue0->sing[1] + StateC0->Prologue0->sing[1] + StateC0->HeapCell0->sing[3] + StateC0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->Epilogue0->sing[1] + StateC0->Prologue0->sing[1] + StateC0->HeapCell0->sing[0] + StateC0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->Epilogue0->sing[4] + StateC0->Prologue0->sing[0] + StateC0->HeapCell0->sing[1] + StateC0->Epilogue0->sing[4]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateC0->HeapCell0->Prologue0 + StateC0->Epilogue0->HeapCell0
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->Epilogue0 + StateC0->Prologue0->HeapCell0 + StateC0->HeapCell0->Epilogue0
    size = StateB0->sing[0]
    toRealloc = StateB0->HeapCell0
    no fit
}

inst size_zero_coalesce {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    blocks = StateA0->Epilogue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell0 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->HeapCell1->sing[2] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[3] + StateB0->HeapCell1->sing[2] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[5] + StateC0->Prologue0->sing[1]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[0] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[0] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[6] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[4] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[6] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[4] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[6] + StateC0->HeapCell0->sing[1] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell1 + StateA0->HeapCell0->Prologue0 + StateA0->HeapCell1->HeapCell0 + StateB0->Epilogue0->HeapCell1 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateC0->Epilogue0->HeapCell0 + StateC0->HeapCell0->Prologue0
    next = StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->Epilogue0 + StateA0->Prologue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateC0->HeapCell0->Epilogue0 + StateC0->Prologue0->HeapCell0
    size = StateB0->sing[0]
    toRealloc = StateB0->HeapCell0
    fit = StateB0->HeapCell1
}

inst smaller {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Epilogue0 + StateC0->Prologue0 + StateC0->HeapCell0 + StateC0->HeapCell1 + StateC0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[2] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[1] + StateC0->Prologue0->sing[1] + StateC0->HeapCell0->sing[2] + StateC0->HeapCell1->sing[1] + StateC0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[0] + StateB0->Epilogue0->sing[1] + StateC0->Prologue0->sing[1] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[0] + StateC0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[3] + StateB0->Epilogue0->sing[4] + StateC0->Prologue0->sing[0] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[3] + StateC0->Epilogue0->sing[4]
    prev = StateA0->Epilogue0->HeapCell0 + StateA0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell1 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell0->Prologue0 + StateC0->HeapCell1->HeapCell0
    next = StateA0->HeapCell0->Epilogue0 + StateA0->Prologue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateC0->HeapCell0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell0
    size = StateB0->sing[2]
    toRealloc = StateB0->HeapCell0
    no fit
}

inst no_fit_test {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    blocks = StateA0->Epilogue0 + StateA0->HeapCell1 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell0 + StateC0->HeapCell1 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell1->sing[2] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[2] + StateB0->HeapCell1->sing[3] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[2] + StateC0->HeapCell1->sing[3] + StateC0->Prologue0->sing[1]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[0] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[3] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[6] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[3] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[6] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[3] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell1 + StateA0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell1 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell0->Prologue0 + StateC0->HeapCell1->HeapCell0
    next = StateA0->HeapCell1->Epilogue0 + StateA0->Prologue0->HeapCell1 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateC0->HeapCell0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell0
    size = StateB0->sing[3]
    toRealloc = StateB0->HeapCell1
    no fit
}

inst new_malloc_test {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1 + HeapCell2
    blocks = StateA0->Epilogue0 + StateA0->HeapCell1 + StateA0->HeapCell2 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell0 + StateC0->HeapCell1 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[4] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[1]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[0] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[0] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[6] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[2] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[6] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[6] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[1] + StateC0->HeapCell1->sing[2] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell2 + StateA0->HeapCell1->Prologue0 + StateA0->HeapCell2->HeapCell1 + StateB0->Epilogue0->HeapCell1 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell0->Prologue0 + StateC0->HeapCell1->HeapCell0
    next = StateA0->HeapCell1->HeapCell2 + StateA0->HeapCell2->Epilogue0 + StateA0->Prologue0->HeapCell1 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateC0->HeapCell0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell0
    size = StateB0->sing[4]
    toRealloc = StateB0->HeapCell1
    fit = StateB0->HeapCell2
}

inst new_split {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1 + HeapCell2 + HeapCell3
    blocks = StateA0->Epilogue0 + StateA0->HeapCell2 + StateA0->HeapCell3 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->HeapCell2 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell0 + StateC0->HeapCell1 + StateC0->HeapCell2 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell2->sing[1] + StateA0->HeapCell3->sing[3] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->HeapCell2->sing[2] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[2] + StateC0->HeapCell2->sing[2] + StateC0->Prologue0->sing[1]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell2->sing[1] + StateA0->HeapCell3->sing[0] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->HeapCell2->sing[1] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[0] + StateC0->HeapCell1->sing[0] + StateC0->HeapCell2->sing[1] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[5] + StateA0->HeapCell2->sing[1] + StateA0->HeapCell3->sing[2] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[5] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->HeapCell2->sing[1] + StateB0->HeapCell2->sing[2] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[5] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[2] + StateC0->HeapCell2->sing[1] + StateC0->HeapCell2->sing[2] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell3 + StateA0->HeapCell2->Prologue0 + StateA0->HeapCell3->HeapCell2 + StateB0->Epilogue0->HeapCell1 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell2 + StateB0->HeapCell2->HeapCell0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell0->Prologue0 + StateC0->HeapCell1->HeapCell2 + StateC0->HeapCell2->HeapCell0
    next = StateA0->HeapCell2->HeapCell3 + StateA0->HeapCell3->Epilogue0 + StateA0->Prologue0->HeapCell2 + StateB0->HeapCell0->HeapCell2 + StateB0->HeapCell1->Epilogue0 + StateB0->HeapCell2->HeapCell1 + StateB0->Prologue0->HeapCell0 + StateC0->HeapCell0->HeapCell2 + StateC0->HeapCell1->Epilogue0 + StateC0->HeapCell2->HeapCell1 + StateC0->Prologue0->HeapCell0
    size = StateB0->sing[2]
    toRealloc = StateB0->HeapCell2
    fit = StateB0->HeapCell3
}

inst new_split_fail {
    boiler
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1 + HeapCell2
    blocks = StateA0->Epilogue0 + StateA0->HeapCell1 + StateA0->HeapCell2 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell0 + StateC0->HeapCell1 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[3] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->HeapCell2->sing[2] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[2] + StateC0->HeapCell2->sing[2] + StateC0->Prologue0->sing[1]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[0] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[0] + StateC0->HeapCell1->sing[0] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[5] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[2] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[5] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->HeapCell1->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[5] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell0->sing[1] + StateC0->HeapCell1->sing[2] + StateC0->HeapCell2->sing[3] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell2 + StateA0->HeapCell1->Prologue0 + StateA0->HeapCell2->HeapCell1 + StateB0->Epilogue0->HeapCell1 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell1 + StateB0->HeapCell1->HeapCell0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell0->Prologue0 + StateC0->HeapCell1->HeapCell1 + StateC0->HeapCell1->HeapCell0
    next = StateA0->HeapCell1->HeapCell2 + StateA0->HeapCell2->Epilogue0 + StateA0->Prologue0->HeapCell1 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue0 + StateB0->HeapCell2->HeapCell1 + StateB0->Prologue0->HeapCell0 + StateC0->HeapCell0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->HeapCell2->HeapCell1 + StateC0->Prologue0->HeapCell0
    size = StateB0->sing[2]
    toRealloc = StateB0->HeapCell1
    fit = StateB0->HeapCell2
}

test expect {
    test0: {best_fit_realloc} for size_equal is sat
    test1: {best_fit_realloc} for size_zero is sat
    test2: {best_fit_realloc} for size_zero_coalesce is sat
    test3: {best_fit_realloc} for smaller is sat
    test4: {best_fit_realloc} for no_fit_test is sat
    test5: {best_fit_realloc} for new_malloc_test is sat
    test6: {best_fit_realloc} for new_split is sat
    test7: {best_fit_realloc} for new_split_fail is unsat
 }