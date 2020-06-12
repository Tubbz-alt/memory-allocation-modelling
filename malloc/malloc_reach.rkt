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
  flist: set HeapCell,
  flist_first: lone HeapCell,
  flist_end: lone HeapCell,
  flist_next: set HeapCell -> HeapCell,
  flist_prev: set HeapCell -> HeapCell,
  heapSize: one Int --get current size (in terms of words) of the HeapCell (later assert that it is equal to sum of all blocks)
}

--MIGHT JUST DO TWO STATES: BEFORE AND AFTER, Decide which algorithm in testing
one sig StateA extends State {}
one sig StateB extends State {
    size: one Int,
    fit: set HeapCell
}

-----VALIDITY PREDS-------

--memory can only be a HeapCell, Prologue, or Epilogue
pred abstractHeapCell {
  HeapCell = Prologue + HeapCell + Epilogue
}

--only these  states appear in the model, each pred will be a state A to B transition
pred abstractState {
  State = StateA + StateB
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

--create a circular, doubly-linked free list
pred free_list[s: State] {
    all cell: HeapCell | cell in s.flist iff cell.(s.allocated) = sing[0]
    all cell: HeapCell | {
        sum[cell.(s.pointers)] = min[s.flist.(s.pointers)] iff cell = s.flist_first
        sum[cell.(s.pointers)] = max[s.flist.(s.pointers)] iff cell = s.flist_end
    }
    s.flist_end.(s.flist_next) = s.flist_first
    s.flist_first.(s.flist_prev) = s.flist_end
    all c1, c2 : HeapCell | {
        c1 in s.flist - s.flist_first and c2 in s.flist - s.flist_end and sum[c1.(s.pointers)] > sum[c2.(s.pointers)] implies c2 in c1.^(s.flist_next) and c1 in c2.^(s.flist_next)
    }
    all cell : s.flist | {
        one cell.(s.flist_next)
        one (s.flist_next).cell
        cell.(s.flist_prev) = (s.flist_next).cell --establishes everything in next and prev, prev is constrained as opposite of next
    }
    all cell : HeapCell - s.flist | {
        no cell.(s.flist_next)
        no (s.flist_next).cell
        no cell.(s.flist_prev)
        no (s.flist_prev).cell
    }
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
    free_list[s]
}

--run { validState[StateA] and validState[StateB]} for exactly 7 HeapCell, 2 State, 4 Int

pred malloc[new : HeapCell, oldFree : HeapCell] {
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks - oldFree + new
    StateB.next = StateA.next - oldFree -> oldFree.(StateA.next) - oldFree.(StateA.prev) -> oldFree + oldFree.(StateA.prev) -> new + new -> oldFree.(StateA.next)
    StateB.prev = StateA.prev - oldFree -> oldFree.(StateA.prev) - oldFree.(StateA.next) -> oldFree + oldFree.(StateA.next) -> new + new -> oldFree.(StateA.prev)
    StateB.sizes = StateA.sizes - oldFree -> oldFree.(StateA.sizes) + new -> StateB.size
    StateB.pointers = StateA.pointers - oldFree -> oldFree.(StateA.pointers) + new -> oldFree.(StateA.pointers)
    StateB.allocated = StateA.allocated - oldFree -> sing[0] + new -> sing[1]
    StateB.flist = StateA.flist - oldFree
    oldFree = StateA.flist_first implies StateB.flist_first = oldFree.(StateA.flist_next)
    not oldFree = StateA.flist_first and not #StateB.flist = 0 implies StateB.flist_first = StateA.flist_first
    oldFree = StateA.flist_end implies StateB.flist_end = oldFree.(StateA.flist_prev)
    not oldFree = StateA.flist_end and not #StateB.flist = 0 implies StateB.flist_end = StateA.flist_end
    #StateB.flist = 0 implies no StateB.flist_next and no StateB.flist_prev and no StateB.flist_first and no StateB.flist_end
    #StateB.flist > 0 implies {
        StateB.flist_next = StateA.flist_next - oldFree -> oldFree.(StateA.flist_next) - oldFree.(StateA.flist_prev) -> oldFree + oldFree.(StateA.flist_prev) -> oldFree.(StateA.flist_next)
        StateB.flist_prev = StateA.flist_prev - oldFree -> oldFree.(StateA.flist_prev) - oldFree.(StateA.flist_next) -> oldFree + oldFree.(StateA.flist_next) -> oldFree.(StateA.flist_prev)
    }
}

pred addCellToEnd[new : HeapCell] {
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks + new
    StateB.next = StateA.next - (StateA.epilogue.(StateA.prev) -> StateA.epilogue) + (StateA.epilogue.(StateA.prev) -> new) + (new -> StateB.epilogue)
    StateB.prev = StateA.prev - StateA.epilogue -> StateA.epilogue.(StateA.prev) + StateA.epilogue -> new + new -> StateA.epilogue.(StateA.prev)
    StateB.sizes = StateA.sizes + new -> StateB.size
    StateB.pointers = StateA.pointers - StateA.epilogue -> StateA.epilogue.(StateA.pointers) + new -> StateA.epilogue.(StateA.pointers) + StateB.epilogue -> sing[add[sum[StateA.epilogue.(StateA.pointers)], sum[StateB.size]]]
    StateB.allocated = StateA.allocated + new -> sing[1]
    StateB.flist = StateA.flist
    StateB.flist_first = StateA.flist_first
    StateB.flist_end = StateA.flist_end
    StateB.flist_next = StateA.flist_next
    StateB.flist_prev = StateA.flist_prev
}

pred split[new : HeapCell, oldFree: HeapCell] {
    -- Fill me in!
    some newFree : HeapCell | {
        newFree not in StateA.blocks
        StateB.prologue = StateA.prologue
        StateB.epilogue = StateA.epilogue
        StateB.blocks = StateA.blocks - oldFree + new + newFree
        StateB.next = StateA.next - oldFree -> oldFree.(StateA.next) - oldFree.(StateA.prev) -> oldFree + oldFree.(StateA.prev) -> new + new -> newFree + newFree -> oldFree.(StateA.next)
        StateB.prev = StateA.prev - oldFree -> oldFree.(StateA.prev) - oldFree.(StateA.next) -> oldFree + oldFree.(StateA.next) -> newFree + newFree -> new + new -> oldFree.(StateA.prev)
        StateB.sizes = StateA.sizes - oldFree -> oldFree.(StateA.sizes) + new -> StateB.size + newFree -> sing[subtract[sum[oldFree.(StateA.sizes)], sum[new.(StateB.sizes)]]]
        StateB.pointers = StateA.pointers - oldFree -> oldFree.(StateA.pointers) + new -> oldFree.(StateA.pointers) + newFree -> sing[add[sum[new.(StateB.pointers)], sum[new.(StateB.sizes)]]]
        StateB.allocated = StateA.allocated - oldFree -> sing[0] + new -> sing[1] + newFree -> sing[0]
        StateB.flist = StateA.flist + newFree - oldFree
        sum[newFree.(StateB.pointers)] = min[StateB.flist.(StateB.pointers)] implies StateB.flist_first = newFree
        not sum[newFree.(StateB.pointers)] = min[StateB.flist.(StateB.pointers)] implies StateB.flist_first = StateA.flist_first
        sum[newFree.(StateB.pointers)] = max[StateB.flist.(StateB.pointers)] implies StateB.flist_end = newFree
        not sum[newFree.(StateB.pointers)] = max[StateB.flist.(StateB.pointers)] implies StateB.flist_end = StateA.flist_end
        #StateB.flist = 1 implies StateB.flist_next = newFree -> newFree and StateB.flist_prev = newFree -> newFree
        #StateB.flist > 1 implies {
        StateB.flist_next = StateA.flist_next - oldFree -> oldFree.(StateA.flist_next) - oldFree.(StateA.flist_prev) -> oldFree + newFree -> oldFree.(StateA.flist_next) + oldFree.(StateA.flist_prev) -> newFree
        StateB.flist_prev = StateA.flist_prev - oldFree -> oldFree.(StateA.flist_prev) - oldFree.(StateA.flist_next) -> oldFree + newFree -> oldFree.(StateA.flist_prev) + oldFree.(StateA.flist_next) -> newFree
           }
     }
}

--best-fit malloc, get free block and either malloc, add to end (sbrk), or split
pred best_fit_malloc {
    StateB.heapSize = StateA.heapSize
    sum[StateB.size] >= 0
    all cell : StateB.blocks | {
        { sum c : cell.*(StateB.prev) | sum[c.(StateB.sizes)] }  <= sum[StateB.heapSize]
        { sum c : cell.^(StateB.prev) | sum[c.(StateB.sizes)] } < { sum c : cell.*(StateB.prev) | sum[c.(StateB.sizes)] }
    }
     all cell : HeapCell | cell in StateB.fit iff cell in StateA.flist and sum[cell.(StateA.sizes)] >= sum[StateB.size]
    sum[StateB.size] = 0 implies {
        StateB.blocks = StateA.blocks
        StateB.sizes = StateA.sizes
        StateB.pointers = StateA.pointers
        StateB.allocated = StateA.allocated
        StateB.prologue = StateA.prologue
        StateB.epilogue = StateA.epilogue
        StateB.next = StateA.next
        StateB.prev = StateA.prev
        StateB.flist = StateA.flist
        StateB.flist_first = StateA.flist_first
        StateB.flist_end = StateA.flist_end
        StateB.flist_next = StateA.flist_next
        StateB.flist_prev = StateA.flist_prev
    }
    sum[StateB.size] > 0 implies {
        some newCell : HeapCell | {
            newCell not in StateA.blocks
            no StateB.fit implies addCellToEnd[newCell]
            all best : StateB.fit | {
                    sum[best.(StateA.sizes)] = min[StateB.fit.(StateA.sizes)] and min[StateB.fit.(StateA.sizes)] = sum[StateB.size] implies malloc[newCell, best]
                    sum[best.(StateA.sizes)] = min[StateB.fit.(StateA.sizes)] and min[StateB.fit.(StateA.sizes)] > sum[StateB.size] implies split[newCell, best]
            }
        }
    }
}


--run { validState[StateA]} for 6 HeapCell, 2 State, 4 Int
consistent: check { (validState[StateA] and best_fit_malloc) implies validState[StateB] } for exactly 7 HeapCell, exactly 2 State, exactly 4 Int
