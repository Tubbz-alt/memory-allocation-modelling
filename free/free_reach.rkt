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
    toFree: lone HeapCell
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
    StateC.flist = StateB.flist - curr - nxt
    sum[pre.(StateB.pointers)] = min[StateC.flist.(StateB.pointers)] implies StateC.flist_first = pre
    not sum[pre.(StateB.pointers)] = min[StateC.flist.(StateB.pointers)] implies StateC.flist_first = StateB.flist_first
    sum[pre.(StateB.pointers)] = max[StateC.flist.(StateB.pointers)] implies StateC.flist_end = pre
    not sum[pre.(StateB.pointers)] = max[StateC.flist.(StateB.pointers)] implies StateC.flist_end = StateB.flist_end
    #StateC.flist = 1 implies StateC.flist_next = pre -> pre and StateC.flist_prev = pre -> pre
    #StateC.flist = 2 implies {
         pre = StateC.flist_first implies StateC.flist_next = StateB.flist_end -> pre + pre -> StateB.flist_end
                                                   and StateC.flist_prev = StateB.flist_end -> pre + pre -> StateB.flist_end
         pre = StateC.flist_end implies StateC.flist_next = StateB.flist_first -> pre + pre -> StateA.flist_first
                                                and StateC.flist_prev = StateB.flist_first -> pre + pre -> StateB.flist_first
     }
     #StateC.flist > 2 implies {
        pre = StateC.flist_first implies {
            StateC.flist_next = StateB.flist_next - StateB.flist_end -> StateB.flist_first + StateC.flist_first -> StateB.flist_first + StateB.flist_end -> StateC.flist_first
            StateC.flist_prev = StateB.flist_prev - StateB.flist_first -> StateB.flist_end + StateB.flist_first -> StateC.flist_first + StateC.flist_first -> StateB.flist_end
        }
        pre = StateC.flist_end implies {
            StateC.flist_next = StateB.flist_next - StateB.flist_end -> StateB.flist_first + StateB.flist_end -> StateC.flist_end + StateC.flist_end -> StateB.flist_first
            StateC.flist_prev = StateB.flist_prev - StateB.flist_first -> StateB.flist_end + StateB.flist_first -> StateC.flist_end + StateC.flist_end -> StateB.flist_end
        }
        not pre = StateC.flist_first and not pre = StateC.flist_end implies {
            all c1, c2: StateC.flist | sum[c1.(StateC.pointers)] < sum[pre.(StateC.pointers)] and sum[c2.(StateC.pointers)] > sum[pre.(StateC.pointers)] implies {
                StateC.flist_next = StateB.flist_next - c1 -> c2 + c1 -> pre + pre -> c2
                StateC.flist_prev = StateB.flist_prev - c2 -> c1 + pre -> c1 + c2 -> pre
            }
        }
    }
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
    StateC.flist = StateB.flist - curr
    sum[pre.(StateB.pointers)] = min[StateC.flist.(StateB.pointers)] implies StateC.flist_first = pre
    not sum[pre.(StateB.pointers)] = min[StateC.flist.(StateB.pointers)] implies StateC.flist_first = StateC.flist_first
    sum[pre.(StateB.pointers)] = max[StateC.flist.(StateB.pointers)] implies StateC.flist_end = pre
    not sum[pre.(StateB.pointers)] = max[StateC.flist.(StateB.pointers)] implies StateC.flist_end = StateB.flist_end
    #StateC.flist = 1 implies StateC.flist_next = pre -> pre and StateC.flist_prev = pre -> pre
    #StateC.flist = 2 implies {
         pre = StateC.flist_first implies StateC.flist_next = StateB.flist_end -> pre + pre -> StateB.flist_end
                                                   and StateC.flist_prev = StateB.flist_end -> pre + pre -> StateB.flist_end
         pre = StateC.flist_end implies StateC.flist_next = StateB.flist_first -> pre + pre -> StateB.flist_first
                                                and StateC.flist_prev = StateB.flist_first -> pre + pre -> StateB.flist_first
     }
     #StateC.flist > 2 implies {
        pre = StateC.flist_first implies {
            StateC.flist_next = StateB.flist_next - StateB.flist_end -> StateB.flist_first + StateC.flist_first -> StateB.flist_first + StateB.flist_end -> StateC.flist_first
            StateC.flist_prev = StateB.flist_prev - StateB.flist_first -> StateB.flist_end + StateB.flist_first -> StateC.flist_first + StateC.flist_first -> StateB.flist_end
        }
        pre = StateC.flist_end implies {
            StateC.flist_next = StateB.flist_next - StateB.flist_end -> StateB.flist_first + StateB.flist_end -> StateC.flist_end + StateC.flist_end -> StateB.flist_first
            StateC.flist_prev = StateB.flist_prev - StateB.flist_first -> StateB.flist_end + StateB.flist_first -> StateC.flist_end + StateC.flist_end -> StateB.flist_end
        }
        not pre = StateC.flist_first and not pre = StateC.flist_end implies {
            all c1, c2: StateC.flist | sum[c1.(StateC.pointers)] < sum[pre.(StateC.pointers)] and sum[c2.(StateC.pointers)] > sum[pre.(StateC.pointers)] implies {
                StateC.flist_next = StateB.flist_next - c1 -> c2 + c1 -> pre + pre -> c2
                StateC.flist_prev = StateB.flist_prev - c2 -> c1 + pre -> c1 + c2 -> pre
            }
        }
    }
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
    StateC.flist = StateB.flist - nxt
    sum[curr.(StateB.pointers)] = min[StateC.flist.(StateB.pointers)] implies StateC.flist_first = curr
    not sum[curr.(StateB.pointers)] = min[StateC.flist.(StateB.pointers)] implies StateC.flist_first = StateB.flist_first
    sum[curr.(StateB.pointers)] = max[StateC.flist.(StateB.pointers)] implies StateC.flist_end = curr
    not sum[curr.(StateB.pointers)] = max[StateC.flist.(StateB.pointers)] implies StateC.flist_end = StateB.flist_end
    #StateC.flist = 1 implies StateC.flist_next = curr -> curr and StateC.flist_prev = curr -> curr
    #StateC.flist = 2 implies {
         curr= StateC.flist_first implies StateC.flist_next = StateB.flist_end -> curr+ curr-> StateB.flist_end
                                                   and StateC.flist_prev = StateB.flist_end -> curr+ curr-> StateA.flist_end
         curr = StateC.flist_end implies StateC.flist_next = StateB.flist_first -> curr + curr -> StateA.flist_first
                                                and StateC.flist_prev = StateB.flist_first -> curr + curr -> StateA.flist_first
     }
     #StateC.flist > 2 implies {
        curr = StateC.flist_first implies {
            StateC.flist_next = StateB.flist_next - StateB.flist_end -> StateB.flist_first + StateC.flist_first -> StateB.flist_first + StateB.flist_end -> StateC.flist_first
            StateC.flist_prev = StateB.flist_prev - StateB.flist_first -> StateB.flist_end + StateB.flist_first -> StateC.flist_first + StateC.flist_first -> StateB.flist_end
        }
        curr = StateC.flist_end implies {
            StateC.flist_next = StateB.flist_next - StateB.flist_end -> StateB.flist_first + StateB.flist_end -> StateC.flist_end + StateC.flist_end -> StateB.flist_first
            StateC.flist_prev = StateB.flist_prev - StateB.flist_first -> StateB.flist_end + StateB.flist_first -> StateC.flist_end + StateC.flist_end -> StateB.flist_end
        }
        not curr = StateC.flist_first and not curr = StateC.flist_end implies {
            all c1, c2: StateC.flist | sum[c1.(StateC.pointers)] < sum[curr.(StateC.pointers)] and sum[c2.(StateC.pointers)] > sum[curr.(StateC.pointers)] implies {
                StateC.flist_next = StateB.flist_next - c1 -> c2 + c1 -> curr + curr -> c2
                StateC.flist_prev = StateB.flist_prev - c2 -> c1 + curr -> c1 + c2 -> curr
            }
        }
    }
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
        StateC.flist = StateB.flist
        StateC.flist_first = StateB.flist_first
        StateC.flist_end = StateB.flist_end
        StateC.flist_next = StateB.flist_next
        StateC.flist_prev = StateB.flist_prev
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
    no StateB.toFree implies {
        StateB.prologue = StateA.prologue
        StateB.epilogue = StateA.epilogue
        StateB.blocks = StateA.blocks
        StateB.next = StateA.next
        StateB.prev = StateA.prev
        StateB.sizes = StateA.sizes
        StateB.pointers = StateA.pointers
        StateB.allocated = StateA.allocated
        StateB.heapSize = StateA.heapSize
        StateB.flist = StateA.flist
        StateB.flist_first = StateA.flist_first
        StateB.flist_end = StateA.flist_end
        StateB.flist_next = StateA.flist_next
        StateB.flist_prev = StateA.flist_prev
        StateC.prologue = StateB.prologue
        StateC.epilogue = StateB.epilogue
        StateC.blocks = StateB.blocks
        StateC.next = StateB.next
        StateC.prev = StateB.prev
        StateC.sizes = StateB.sizes
        StateC.pointers = StateB.pointers
        StateC.allocated = StateB.allocated
        StateC.heapSize = StateB.heapSize
        StateC.flist = StateB.flist
        StateC.flist_first = StateB.flist_first
        StateC.flist_end = StateB.flist_end
        StateC.flist_next = StateB.flist_next
        StateC.flist_prev = StateB.flist_prev
    }
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
    StateB.flist = StateA.flist + StateB.toFree
    sum[StateB.toFree.(StateB.pointers)] = min[StateB.flist.(StateB.pointers)] implies StateB.flist_first = StateB.toFree
    not sum[StateB.toFree.(StateB.pointers)] = min[StateB.flist.(StateB.pointers)] implies StateB.flist_first = StateA.flist_first
    sum[StateB.toFree.(StateB.pointers)] = max[StateB.flist.(StateB.pointers)] implies StateB.flist_end = StateB.toFree
    not sum[StateB.toFree.(StateB.pointers)] = max[StateB.flist.(StateB.pointers)] implies StateB.flist_end = StateA.flist_end
     #StateB.flist = 1 implies StateB.flist_next = StateB.toFree -> StateB.toFree and StateB.flist_prev = StateB.toFree -> StateB.toFree
     #StateB.flist = 2 implies {
         StateB.toFree = StateB.flist_first implies StateB.flist_next = StateA.flist_end -> StateB.toFree + StateB.toFree -> StateA.flist_end
                                                   and StateB.flist_prev = StateA.flist_end -> StateB.toFree + StateB.toFree -> StateA.flist_end
         StateB.toFree = StateB.flist_end implies StateB.flist_next = StateA.flist_first -> StateB.toFree + StateB.toFree -> StateA.flist_first
                                                and StateB.flist_prev = StateA.flist_first -> StateB.toFree + StateB.toFree -> StateA.flist_first
     }
     #StateB.flist > 2 implies {
        StateB.toFree = StateB.flist_first implies {
            StateB.flist_next = StateA.flist_next - StateA.flist_end -> StateA.flist_first + StateB.flist_first -> StateA.flist_first + StateA.flist_end -> StateB.flist_first
            StateB.flist_prev = StateA.flist_prev - StateA.flist_first -> StateA.flist_end + StateA.flist_first -> StateB.flist_first + StateB.flist_first -> StateA.flist_end
        }
        StateB.toFree = StateB.flist_end implies {
            StateB.flist_next = StateA.flist_next - StateA.flist_end -> StateA.flist_first + StateA.flist_end -> StateB.flist_end + StateB.flist_end -> StateA.flist_first
            StateB.flist_prev = StateA.flist_prev - StateA.flist_first -> StateA.flist_end + StateA.flist_first -> StateB.flist_end + StateB.flist_end -> StateA.flist_end
        }
        not StateB.toFree = StateB.flist_first and not StateB.toFree = StateB.flist_end implies {
            all c1, c2: StateB.flist | sum[c1.(StateB.pointers)] < sum[StateB.toFree.(StateB.pointers)] and sum[c2.(StateB.pointers)] > sum[StateB.toFree.(StateB.pointers)] implies {
                StateB.flist_next = StateA.flist_next - c1 -> c2 + c1 -> StateB.toFree + StateB.toFree -> c2
                StateB.flist_prev = StateA.flist_prev - c2 -> c1 + StateB.toFree -> c1 + c2 -> StateB.toFree
            }
        }
    }
    coalesce[StateB.toFree]
}


--run { validState[StateA] and free} for 5 HeapCell, 3 State, 4 Int
--consistent: check { (validState[StateA] and free) implies validState[StateB] } for 5 HeapCell, exactly 3 State, exactly 4 Int --should fail for not coalesced
consistentCoalesce: check { (validState[StateA] and free) implies validState[StateC] } for 7 HeapCell, exactly 2 State, exactly 4 Int --should fail for not coalesced
