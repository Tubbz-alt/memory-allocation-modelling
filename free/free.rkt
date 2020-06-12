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
    toFree: one HeapCell
}
one sig StateC extends State {} --used for coalescing

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

--prev and next are both free
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

--pre is free
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

--next is free
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

--set toFree block to not be allocated
pred free {
    all cell : HeapCell | StateB.toFree = cell iff cell in StateA.blocks and not cell = StateA.epilogue and not cell = StateA.prologue and cell.(StateA.allocated) = sing[1]  --ensures pointer is from set of pointers in pre state heap
    StateB.prologue = StateA.prologue
    StateB.epilogue = StateA.epilogue
    StateB.blocks = StateA.blocks
    StateB.next = StateA.next
    StateB.prev = StateA.prev
    StateB.sizes = StateA.sizes
    StateB.pointers = StateA.pointers
    StateB.allocated = StateA.allocated - StateB.toFree -> sing[1] + StateB.toFree -> sing[0]
    StateB.heapSize = StateA.heapSize
    coalesce[StateB.toFree]
}

run { validState[StateA] and free} for 7 HeapCell, 3 State, exactly 4 Int
consistent: check { (validState[StateA] and free) implies validState[StateB] } for 7 HeapCell, 3 State, exactly 4 Int --should have counterexamples with cells not coalesced
consistentCoalesce: check { (validState[StateA] and free) implies validState[StateC] } for 7 HeapCell, 3 State, exactly 4 Int

------------------------ TESTING SECTION ------------------------

-- Tests that if sum of heap cells is over 7 then that results in
-- heap overflow and returns unsat
inst heapOverFlowTest {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->Epilogue0 + StateC0->Prologue0 + StateC0->HeapCell0 + StateC0->Epilogue0
    sizes = StateA0->Prologue0->5 + StateA0->HeapCell0->3 + StateA0->Epilogue0->1 + StateB0->Prologue0->1 + StateB0->HeapCell0->3 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 + StateC0->HeapCell0->3 + StateC0->Epilogue0->1
    heapSize = StateA0->7 + StateB0->7 + StateC0->7
    allocated = StateA0->Prologue0->1 + StateA0->HeapCell0->1 + StateA0->Epilogue0->1 + StateB0->Prologue0->1 + StateB0->HeapCell0->0 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 + StateC0->HeapCell0->0 + StateC0->Epilogue0->1
    pointers = StateA0->Prologue0->0 + StateA0->HeapCell0->1 + StateA0->Epilogue0->4 + StateB0->Prologue0->0 + StateB0->HeapCell0->1 + StateB0->Epilogue0->4 + StateC0->Prologue0->0 + StateC0->HeapCell0->1 + StateC0->Epilogue0->4
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateC0->HeapCell0->Prologue0 + StateC0->Epilogue0->HeapCell0
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->Epilogue0 + StateC0->Prologue0->HeapCell0 + StateC0->HeapCell0->Epilogue0
    toFree = StateB0->HeapCell0      
}

-- Tests that free works appropriately on a valid state A where no
-- coalescing is needed
inst noCoalescingSatTest {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->Epilogue0 + StateC0->Prologue0 + StateC0->HeapCell0 + StateC0->Epilogue0
    sizes = StateA0->Prologue0->1 + StateA0->HeapCell0->3 + StateA0->Epilogue0->1 + StateB0->Prologue0->1 + StateB0->HeapCell0->3 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 + StateC0->HeapCell0->3 + StateC0->Epilogue0->1
    heapSize = StateA0->7 + StateB0->7 + StateC0->7
    allocated = StateA0->Prologue0->1 + StateA0->HeapCell0->1 + StateA0->Epilogue0->1 + StateB0->Prologue0->1 + StateB0->HeapCell0->0 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 + StateC0->HeapCell0->0 + StateC0->Epilogue0->1
    pointers = StateA0->Prologue0->0 + StateA0->HeapCell0->1 + StateA0->Epilogue0->4 + StateB0->Prologue0->0 + StateB0->HeapCell0->1 + StateB0->Epilogue0->4 + StateC0->Prologue0->0 + StateC0->HeapCell0->1 + StateC0->Epilogue0->4
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateC0->HeapCell0->Prologue0 + StateC0->Epilogue0->HeapCell0
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->Epilogue0 + StateC0->Prologue0->HeapCell0 + StateC0->HeapCell0->Epilogue0
    toFree = StateB0->HeapCell0      
}

-- Tests that if nothing is freed then the free predicate is unsat
inst noCoalescingUnsatTest {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->Epilogue0 + StateC0->Prologue0 + StateC0->HeapCell0 + StateC0->Epilogue0
    sizes = StateA0->Prologue0->1 + StateA0->HeapCell0->3 + StateA0->Epilogue0->1 + StateB0->Prologue0->1 + StateB0->HeapCell0->3 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 + StateC0->HeapCell0->3 + StateC0->Epilogue0->1
    heapSize = StateA0->7 + StateB0->7 + StateC0->7
    allocated = StateA0->Prologue0->1 + StateA0->HeapCell0->1 + StateA0->Epilogue0->1 + StateB0->Prologue0->1 + StateB0->HeapCell0->1 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 + StateC0->HeapCell0->1 + StateC0->Epilogue0->1
    pointers = StateA0->Prologue0->0 + StateA0->HeapCell0->1 + StateA0->Epilogue0->4 + StateB0->Prologue0->0 + StateB0->HeapCell0->1 + StateB0->Epilogue0->4 + StateC0->Prologue0->0 + StateC0->HeapCell0->1 + StateC0->Epilogue0->4
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateC0->HeapCell0->Prologue0 + StateC0->Epilogue0->HeapCell0
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->Epilogue0 + StateC0->Prologue0->HeapCell0 + StateC0->HeapCell0->Epilogue0
    toFree = StateB0->HeapCell0
}

-- Tests that coalescing not occurring when needed is unsat
inst coalescingUnsatTest {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Prologue0 + StateA0->HeapCell0 + StateA0->Epilogue0 + StateA0->HeapCell1 + StateB0->HeapCell1 + StateB0->Prologue0 + StateB0->HeapCell0 + StateB0->Epilogue0 + StateC0->Prologue0 + StateC0->HeapCell0 + StateC0->HeapCell1 + StateC0->Epilogue0
    sizes = StateA0->HeapCell1->1 + StateA0->Prologue0->1 + StateA0->HeapCell0->3 + StateA0->Epilogue0->1 +  StateB0->HeapCell1->1 + StateB0->Prologue0->1 + StateB0->HeapCell0->3 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 +  StateC0->HeapCell1->1 +StateC0->HeapCell0->3 + StateC0->Epilogue0->1
    heapSize = StateA0->7 + StateB0->7 + StateC0->7 
    allocated = StateA0->Prologue0->1 + StateA0->HeapCell0->1 + StateA0->Epilogue0->1 + StateA0->HeapCell1->0 + StateB0->HeapCell1->0 + StateB0->Prologue0->1 + StateB0->HeapCell0->0 + StateB0->Epilogue0->1 + StateC0->Prologue0->1 + StateC0->HeapCell0->0 + StateC0->Epilogue0->1 + StateC0->HeapCell1->0
    pointers = StateA0->HeapCell1->5 + StateA0->Prologue0->0 + StateA0->HeapCell0->1 + StateA0->Epilogue0->4 + StateB0->HeapCell1->5 + StateB0->Prologue0->0 + StateB0->HeapCell0->1 + StateB0->Epilogue0->4 + StateC0->HeapCell1->5 + StateC0->Prologue0->0 + StateC0->HeapCell0->1 + StateC0->Epilogue0->4
    prev = StateA0->HeapCell0->Prologue0 + StateA0->Epilogue0->HeapCell1 + StateA0->HeapCell1->HeapCell0 + StateB0->HeapCell0->Prologue0 + StateB0->Epilogue0->HeapCell1 + StateB0->HeapCell1->HeapCell0 + StateC0->HeapCell0->Prologue0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell1->HeapCell0 
    next = StateA0->Prologue0->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->Epilogue0 + StateB0->Prologue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell0 + StateC0->HeapCell0->HeapCell1 + StateC0->HeapCell1->Epilogue0
    toFree = StateB0->HeapCell0 
}

-- Tests that coalescing occurs correctly with two blocks where the next is allocated
inst coalescingSatTest {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Epilogue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell1 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[4] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[4] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[5] + StateC0->Prologue0->sing[1]
    heapSize = StateA0->sing[7] + StateB0->sing[7] + StateC0->sing[7]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[0] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[6] + StateA0->HeapCell0->sing[5] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[6] + StateB0->HeapCell0->sing[5] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[6] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Prologue0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell1->Prologue0
    next = StateA0->HeapCell0->Epilogue0 + StateA0->HeapCell1->HeapCell0 + StateA0->Prologue0->HeapCell1 + StateB0->HeapCell0->Epilogue0 + StateB0->HeapCell1->HeapCell0 + StateB0->Prologue0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell1
    toFree = StateB0->HeapCell1
}

-- Tests that coalescing occurs correctly with two blocks where the prev is allocated
inst coalescingSatTestTwo {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Epilogue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell1 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[4] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[4] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[5] + StateC0->Prologue0->sing[1]
    heapSize = StateA0->sing[7] + StateB0->sing[7] + StateC0->sing[7]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[0] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[0] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[6] + StateA0->HeapCell0->sing[5] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[6] + StateB0->HeapCell0->sing[5] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[6] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Prologue0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell1->Prologue0
    next = StateA0->HeapCell0->Epilogue0 + StateA0->HeapCell1->HeapCell0 + StateA0->Prologue0->HeapCell1 + StateB0->HeapCell0->Epilogue0 + StateB0->HeapCell1->HeapCell0 + StateB0->Prologue0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell1
    toFree = StateB0->HeapCell0
}

-- Tests that no existing allocated cell to free up is unsat
inst noFreeTestOne {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Epilogue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell1 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[4] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[4] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[5] + StateC0->Prologue0->sing[1]
    heapSize = StateA0->sing[7] + StateB0->sing[7] + StateC0->sing[7]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->HeapCell1->sing[0] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[0] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[6] + StateA0->HeapCell0->sing[5] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[6] + StateB0->HeapCell0->sing[5] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[6] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Prologue0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell1->Prologue0
    next = StateA0->HeapCell0->Epilogue0 + StateA0->HeapCell1->HeapCell0 + StateA0->Prologue0->HeapCell1 + StateB0->HeapCell0->Epilogue0 + StateB0->HeapCell1->HeapCell0 + StateB0->Prologue0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell1
    toFree = StateB0->HeapCell0
}


-- Tests that no existing allocated cell to free up is unsat
inst noFreeTestTwo {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Epilogue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->Epilogue0 + StateC0->HeapCell1 + StateC0->Prologue0
    sizes = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[4] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[4] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[5] + StateC0->Prologue0->sing[1]
    heapSize = StateA0->sing[7] + StateB0->sing[7] + StateC0->sing[7]
    allocated = StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->HeapCell1->sing[0] + StateA0->Prologue0->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell1->sing[0] + StateC0->Prologue0->sing[1]
    pointers = StateA0->Epilogue0->sing[6] + StateA0->HeapCell0->sing[5] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[0] + StateB0->Epilogue0->sing[6] + StateB0->HeapCell0->sing[5] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[6] + StateC0->HeapCell1->sing[1] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue0->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->Prologue0 + StateB0->Epilogue0->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->Prologue0 + StateC0->Epilogue0->HeapCell1 + StateC0->HeapCell1->Prologue0
    next = StateA0->HeapCell0->Epilogue0 + StateA0->HeapCell1->HeapCell0 + StateA0->Prologue0->HeapCell1 + StateB0->HeapCell0->Epilogue0 + StateB0->HeapCell1->HeapCell0 + StateB0->Prologue0->HeapCell1 + StateC0->HeapCell1->Epilogue0 + StateC0->Prologue0->HeapCell1
    toFree = StateB0->HeapCell1
}

-- Tests that both cells are allocated and need to be freed up up is sat
inst bothFreeTest {
    State = StateA0 + StateB0 + StateC0
    Prologue = Prologue0
    Epilogue = Epilogue0
    HeapCell = Prologue0 + Epilogue0 + HeapCell0 + HeapCell1 + HeapCell2
    prologue = StateA0->Prologue0 + StateB0->Prologue0 + StateC0->Prologue0
    epilogue = StateA0->Epilogue0 + StateB0->Epilogue0 + StateC0->Epilogue0
    blocks = StateA0->Epilogue0 + StateA0->HeapCell0 + StateA0->HeapCell1 + StateA0->HeapCell2 + StateA0->Prologue0 + StateB0->Epilogue0 + StateB0->HeapCell2 + StateB0->HeapCell0 + StateB0->HeapCell1 + StateB0->Prologue0 + StateC0->HeapCell0 + StateC0->Epilogue0 + StateC0->Prologue0
    sizes = StateA0->HeapCell2->sing[1] + StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[1] + StateB0->HeapCell2->sing[1] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[1] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[3] + StateC0->Prologue0->sing[1]
    heapSize = StateA0->sing[7] + StateB0->sing[7] + StateC0->sing[7]
    allocated = StateA0->HeapCell2->sing[0] + StateA0->Epilogue0->sing[1] + StateA0->HeapCell0->sing[0] + StateA0->HeapCell1->sing[1] + StateA0->Prologue0->sing[1] + StateB0->HeapCell2->sing[0] + StateB0->Epilogue0->sing[1] + StateB0->HeapCell0->sing[0] + StateB0->HeapCell1->sing[0] + StateB0->Prologue0->sing[1] + StateC0->Epilogue0->sing[1] + StateC0->HeapCell0->sing[0] + StateC0->Prologue0->sing[1]
    pointers = StateA0->HeapCell2->sing[3] + StateA0->Epilogue0->sing[4] + StateA0->HeapCell0->sing[1] + StateA0->HeapCell1->sing[2] + StateA0->Prologue0->sing[0] + StateB0->HeapCell2->sing[3] + StateB0->Epilogue0->sing[4] + StateB0->HeapCell0->sing[1] + StateB0->HeapCell1->sing[2] + StateB0->Prologue0->sing[0] + StateC0->Epilogue0->sing[4] + StateC0->HeapCell0->sing[1] + StateC0->Prologue0->sing[0]
    prev = StateA0->Epilogue->HeapCell2 + StateA0->HeapCell2->HeapCell1 + StateA0->HeapCell1->HeapCell0 + StateA0->HeapCell0->Prologue + StateB0->Epilogue->HeapCell2 + StateB0->HeapCell2->HeapCell1 + StateB0->HeapCell1->HeapCell0 + StateB0->HeapCell0->Prologue + StateC0->Epilogue0->HeapCell0 + StateC0->HeapCell0->Prologue0
    next = StateA0->Prologue->HeapCell0 + StateA0->HeapCell0->HeapCell1 + StateA0->HeapCell1->HeapCell2 + StateA0->HeapCell2->Epilogue + StateB0->Prologue->HeapCell0 + StateB0->HeapCell0->HeapCell1 + StateB0->HeapCell1->HeapCell2 + StateB0->HeapCell2->Epilogue + StateC0->HeapCell0->Epilogue0 + StateC0->Prologue0->HeapCell0
    toFree = StateB0->HeapCell1
}

test expect {
   heapOverFlowTest: {free} for heapOverFlowTest is unsat
   noCoalescingTestOne: {free} for noCoalescingSatTest is sat
   noCoalescingTestTwo: {free} for noCoalescingUnsatTest is unsat
   coalescingTestOne: {free} for coalescingUnsatTest is unsat
   coalescingTestTwo: {free} for coalescingSatTest is sat
   noFreeTestOne: {free} for noFreeTestOne is unsat
   noFreeTestTwo: {free} for noFreeTestTwo is unsat
   random: {validState[StateC]} for bothFreeTest is sat
   bothFreeTest: {free} for bothFreeTest is sat
 }




