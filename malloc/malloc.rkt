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

--only blocks in the state's heap are in the relations
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

--constraints for the next and prev relations
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

--assures cells do not exceed max heap size
pred max_heapSize[s: State] {
    s.heapSize = sing[7]
    all cell : s.blocks | {
        { sum c : cell.*(s.prev) | sum[c.(s.sizes)] }  <= sum[s.heapSize]
        { sum c : cell.^(s.prev) | sum[c.(s.sizes)] } < { sum c : cell.*(s.prev) | sum[c.(s.sizes)] }
    }
}

--no two free cells are adjacent
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

--malloc'd cell perfectly fits old free cell
pred malloc[new : HeapCell, oldFree : HeapCell] {
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks - oldFree + new
    StateB.next = StateA.next - oldFree -> oldFree.(StateA.next) - oldFree.(StateA.prev) -> oldFree + oldFree.(StateA.prev) -> new + new -> oldFree.(StateA.next)
    StateB.prev = StateA.prev - oldFree -> oldFree.(StateA.prev) - oldFree.(StateA.next) -> oldFree + oldFree.(StateA.next) -> new + new -> oldFree.(StateA.prev)
    StateB.sizes = StateA.sizes - oldFree -> oldFree.(StateA.sizes) + new -> StateB.size
    StateB.pointers = StateA.pointers - oldFree -> oldFree.(StateA.pointers) + new -> oldFree.(StateA.pointers)
    StateB.allocated = StateA.allocated - oldFree -> sing[0] + new -> sing[1]
}

--no best fit cell, add to the end before the epilogue
pred addCellToEnd[new : HeapCell] {
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks + new
    StateB.next = StateA.next - (StateA.epilogue.(StateA.prev) -> StateA.epilogue) + (StateA.epilogue.(StateA.prev) -> new) + (new -> StateB.epilogue)
    StateB.prev = StateA.prev - StateA.epilogue -> StateA.epilogue.(StateA.prev) + StateA.epilogue -> new + new -> StateA.epilogue.(StateA.prev)
    StateB.sizes = StateA.sizes + new -> StateB.size
    StateB.pointers = StateA.pointers - StateA.epilogue -> StateA.epilogue.(StateA.pointers) + new -> StateA.epilogue.(StateA.pointers) + StateB.epilogue -> sing[add[sum[StateA.epilogue.(StateA.pointers)], sum[StateB.size]]]
    StateB.allocated = StateA.allocated + new -> sing[1]
}

--split the old free cell, more space than needed to allocate
pred split[new : HeapCell, oldFree: HeapCell] {
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
        --coalesce[newFree]
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
    all cell : HeapCell | cell in StateB.fit iff cell in StateA.blocks and cell.(StateA.allocated) = sing[0] and sum[cell.(StateA.sizes)] >= sum[StateB.size]
    sum[StateB.size] = 0 implies {
        StateB.blocks = StateA.blocks
        StateB.sizes = StateA.sizes
        StateB.pointers = StateA.pointers
        StateB.allocated = StateA.allocated
        StateB.prologue = StateA.prologue
        StateB.epilogue = StateA.epilogue
        StateB.next = StateA.next
        StateB.prev = StateA.prev
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


run { validState[StateA] and best_fit_malloc } for 7 HeapCell, 2 State, exactly 4 Int
consistent: check { (validState[StateA] and best_fit_malloc) implies validState[StateB] } for 7 HeapCell, 2 State, exactly 4 Int


------------------------ TESTING SECTION ------------------------

inst boiler {
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1 + HeapCell2 + HeapCell3 + HeapCell4
    prologue = StateA0->Prologue0 + StateB0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0
    heapSize = StateA0->sing[7] + StateB0->sing[7]
}

--Unallocated block of correct size is allocated. (SAT)
inst simple_SAT {
    boiler

        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell1 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[3] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[4]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell1
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell1 + StateB0->HeapCell1->Epilogue0

    size = StateB0->sing[3]
}

--Free block is too small to malloc, but we malloc it anyways. (UNSAT)
inst simple_UNSAT {
    boiler

        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell1 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[2] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[3] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[4]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell1
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell1 + StateB0->HeapCell1->Epilogue0

    size = StateB0->sing[3]
}

--Malloced block is added to the end b/c free block is too small. (SAT)
inst add_to_end_free_block_too_small {
    boiler
        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[2] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[2] + StateB0->HeapCell1->sing[3] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[3] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[3] + StateB0->Epilogue0->sing[6]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateB0->Epilogue0->HeapCell1
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue

    size = StateB0->sing[3]
}

--No unallocated blocks, so malloced block is added to the end. (SAT)
inst add_to_end_no_free_blocks {
    boiler
        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[3] + StateB0->HeapCell1->sing[2] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[4] + StateB0->Epilogue0->sing[6]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateB0->Epilogue0->HeapCell1
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue

    size = StateB0->sing[2]
}

--Malloc size of 0, pre and post state should both be valid. No change. (SAT)
inst size_0_malloc {
    boiler
        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[3] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->Epilogue0->sing[4]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell0
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->Epilogue0

    size = StateB0->sing[0]
}

--Mallocing a free block that is too big, so split block (SAT)
inst split_case_test {
    boiler
        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell1 + StateB0->HeapCell2 + StateB0->Epilogue0

    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[5] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[3] + StateB0->HeapCell2->sing[2]+ StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->HeapCell2->sing[0] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[6] + StateB0->Prologue0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->HeapCell2->sing[4] + StateB0->Epilogue0->sing[6]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell1->Prologue0 + StateB0->HeapCell2->HeapCell1 + StateB0->Epilogue0->HeapCell2
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell1 + StateB0->HeapCell1->HeapCell2 + StateB0->HeapCell2->Epilogue0

    size = StateB0->sing[3]
}


--Malloc selects best fit block from a number of valid free blocks. (SAT)
inst best_fit_test {
    boiler

        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->HeapCell2 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->HeapCell3 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[3] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[1] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[3] + StateB0->HeapCell1->sing[1]+ StateB0->HeapCell3->sing[1] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->HeapCell3->sing[1] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[4] + StateA0->HeapCell2->sing[5] + StateA0->Epilogue0->sing[6] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[4] + StateB0->HeapCell3->sing[5] + StateB0->Epilogue0->sing[6]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->HeapCell1->HeapCell0 + StateA0->HeapCell2->HeapCell1 + StateA0->Epilogue0->HeapCell2 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateB0->HeapCell3->HeapCell1 + StateB0->Epilogue0->HeapCell3
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->HeapCell2 + StateA0->HeapCell2->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->HeapCell3 + StateB0->HeapCell3->Epilogue0

    size = StateB0->sing[1]
}

--Malloc selects best fit block, even if it results in a split. (SAT)
inst best_fit_w_split_test {
    boiler

        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->HeapCell2 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->HeapCell3 + StateB0->HeapCell4 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[3] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[1]+ StateB0->HeapCell3->sing[2] + StateB0->HeapCell4->sing[1] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->HeapCell1->sing[1] + StateA0->HeapCell2->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->HeapCell3->sing[1] + StateB0->HeapCell4->sing[0]+ StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[2] + StateA0->HeapCell2->sing[3] + StateA0->Epilogue0->sing[6] + StateB0->Prologue0->sing[0] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->HeapCell3->sing[3] + StateB0->HeapCell4->sing[5] + StateB0->Epilogue0->sing[6]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->HeapCell1->HeapCell0 + StateA0->HeapCell2->HeapCell1 + StateA0->Epilogue0->HeapCell2 + StateB0->HeapCell0->Prologue0 + StateB0->HeapCell1->HeapCell0 + StateB0->HeapCell3->HeapCell1 + StateB0->HeapCell4->HeapCell3 + StateB0->Epilogue0->HeapCell4
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->HeapCell2 + StateA0->HeapCell2->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->HeapCell3 + StateB0->HeapCell3->HeapCell4 + StateB0->HeapCell4->Epilogue0

    size = StateB0->sing[2]
}

--Mallocing a size > 7 results in heap overflow (UNSAT)
inst heap_overflow_UNSAT_test {
    boiler

        blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell1 + StateB0->Epilogue0
    sizes = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[5] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[5] + StateB0->Epilogue0->sing[1]
    allocated = StateA0->Prologue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->Epilogue0->sing[1] + StateB0->Prologue0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[1]
    pointers = StateA0->Prologue0->sing[0] + StateA0->HeapCell0->sing[1] + StateA0->Epilogue0->sing[4] + StateB0->Prologue0->sing[0] + StateB0->HeapCell1->sing[1] + StateB0->Epilogue0->sing[-8]
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell1
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell1 + StateB0->HeapCell1->Epilogue0

    size = StateB0->sing[6]
}

test expect {
    test0: {best_fit_malloc} for simple_SAT is sat
    test1: {best_fit_malloc} for simple_UNSAT is unsat
    test2: {best_fit_malloc} for add_to_end_free_block_too_small is sat
    test3: {best_fit_malloc} for add_to_end_no_free_blocks is sat
    test4: {best_fit_malloc} for size_0_malloc is sat
    test5: {best_fit_malloc} for split_case_test is sat
    test6: {best_fit_malloc} for best_fit_test is sat 
    test7: {best_fit_malloc} for best_fit_w_split_test is sat
    test8: {best_fit_malloc} for heap_overflow_UNSAT_test is unsat
 }


