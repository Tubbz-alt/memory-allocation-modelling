README Final Project: Modeling C Dynamic Memory Allocation Using Forge 

DESIGN:

For this final project, we modeled three of the C dynamic memory allocation functions - malloc, free, and realloc - using three separate Forge specs. With these models, we aimed to show that a heap starting at a valid state will end up in a likewise valid state after it undergoes the state transitions for each of the functions. To do this, each spec operated under a validState predicate that served to both initialize a valid starting state as well as allow us to check consistency in the model (i.e. after the state transitions, the heap is also in a valid state). The State sig was the same in every spec, as well as the validState pred:

-sig State
	blocks: a set of HeapCells that are present in the heap at the current state
	sizes: a relation mapping each HeapCell to its size in the current state
	pointers: a relation mapping each HeapCell to its pointer in the current state (i.e. its address in the heap)
	allocated: a relation mapping each HeapCell to an Int indicating whether or not the HeapCell is allocated in the current state (0 if free, 1 if allocated)
	prologue: a state has one Prologue (sig that extends HeapCell and marks the beginning of the heap)
	epilogue: a state has one Epilogue (sig that extends HeapCell and marks the end of the heap)
	next: a relation mapping each HeapCell to the HeapCell that follows it in the current heap
	prev: a relation mapping each HeapCell to the HeapCell that precedes it in the current heap (thus, the blocks of the heap operate as a doubly linked list)
	heapSize: the maximum size of the heap (serves as a bound to model that we should not have HeapOverflow)

-pred validState
	abstractHeapCell: a HeapCell is either a HeapCell, Prologue, or Epilogue
	abstractState: State is either StateA, StateB, or StateC for free and realloc
	prologue_epilogue: each state has one prologue and one epilogue that are both allocated, have a size of 1
	blocks_valid: each cell in a state's blocks appears once in each relation (i.e. it has one size, one pointer, and one allocated tag that is either 1 or 0. Also, if a cell is not in the set of blocks pertaining to the current state, it will not show up in any of the relations
	next_prev: set up the next and prev relations such that each cell has one next and one prev (they are the opposite of each other). This pred also guarantees that the Prologue does not have a cell that comes before it in the list, and the Epilogue does not have a cell that comes after it
	max_heapSize: guarantees that the sum of sizes of blocks in the current heap does not exceed the maximum heapSize as to prevent instances with HeapOverflow
	coalesced: a free cell is always surrounded by allocated cells so that there is no external fragmentation

Some other design choices that are consistent throughout the spec are that we constrain the model to run for 4 Int (-8, -7, ... , 5, 6, 7 are valid) and the maximum heap size is 7. 

The remainder of this section discusses the differences between the three specs, as well as design choices made in each:

Malloc: 
	The malloc function is modeled as a transition from StateA to StateB, where StateA is a valid state and we would like to show that the constraints of the malloc function imply that StateB is also valid. The best_fit_malloc pred operates under the constraint that there is some HeapCell not in StateA's heap that will be added to StateB's heap according to some size. This size is constrained to not cause HeapOverflow and is assigned arbitrarily to represent the size passed in as an argument to the malloc function call. This spec models a "best-fit" implementation of malloc, such that we search through the HeapCell's for a free block that is large enough to fit a block of the size that we wish to allocate, and we allocate the new block into the minimum-size free block from this "best" set. There are 4 cases that can occur when we malloc, with constraints as follow:
	Case 1: if the size is 0, we do not make any change from StateA to StateB
		For cases 2 - 4, we constrain that there is some block that does not exist in StateA (the malloc'd block)
	Case 2: there are no free cells in StateA that fit the size we wish to allocate, so we add that cell to the end of the list, and adjust the pointers of that cell and the epilogue accordingly
	Case 3: the size of the best-fit cell is exactly large enough to fit the size of the malloc'd cell, so we replace the free cell from StateA with an allocated cell in StateB
	Case 4: the size of the best-fit cell is larger than the size requested, so we split the best-fit cell into an allocated cell with the requested size and a free cell with the remaining space in the block in order to reduce fragmentation

Free: 
	The free function is modeled as a transition from a valid StateA to an invalid StateB (in which the requested block is freed but not coalesced) and a valid StateC, in which all blocks are coalesced. There is a block "toFree" which is allocated in StateA and is meant to be freed in StateB, and the free transition changes the allocated status of this block to 0, meaning it is free. However, it may be the case that there exist multiple free HeapCells directly adjacent to each other in the StateB heap, so we coalesce them in another state transition. Thus, in StateC, the cells needed to be coalesced (either free'd block + prev, freed + next, or freed + both) are joined into one larger block that takes in the pointer of the block that came first in the StateB heap. Therefore, StateC satisfies all requirements of a valid state.

Realloc: 
	The realloc function is modeled, like free, as a transition from a valid StateA to a potentially invalid StateB (in which some block that is freed but not coalesced) and a valid StateC, in which all blocks are coalesced. The realloc function call takes in a pointer and a size to resize the allocated block to, which we model by constraining a "toRealloc" block from the allocated blocks in StateA, as well as a size that would fit in the heap, similar to the StateB.size we constrain in the malloc spec. Similarly to malloc, we also follow a best-fit model in this spec, such that we find a set of free blocks large enough to fit the realloc'd cell if needed. There are several cases for the StateA to StateB transition, in the pred best_fit_realloc:
	Case 1: if the size is 0, we simply free the cell that is requested to realloc
	Case 2: if the size requested to realloc is the same as the size already allocated for that block, StateB is the same as StateA
	Case 3: if the size is larger, we put a free cell in the place of the cell we want to realloc, and follow the same cases as Case 2-4 of malloc (i.e. either add a new cell to the end of the list before the epilogue, fit the cell exactly in place of a previously free cell, or split a previously free cell
However, there is a possibility that after transitioning to StateB, there are newly free cells that are not coalesced with adjacent cells, so we follow constraints to have only coalesced cells in StateC, consistent with the cells previously in StateB, identical to the way we checked for non-coalesced cells in the free spec.



TESTING:

Malloc:
- simple_SAT: this instance shows that a free block of the size to be malloced
              becomes allocated after malloc.
- simple_UNSAT: this instance shows an unsat case to show that blocks have to
                be unallocated before they are able to be malloced.
- Adding a block to the end: this instance shows how a new block is added to end
                            if the free blocks are too small to malloc
- Adding a block to the end (no free): this instance shows how a new block is
                            added to end if there are no free blocks
- Size 0 malloc: this instance shows that a malloc of size 0 will result in no
                 change
- Split case: this instance shows that our spec split a free block that is too
              large into one allocated block and one unallocated block the size
              of the remainder.
- Best fit malloc: this instance shows that our spec chooses the best fit block
                  from a number of valid free blocks.
- Best fit malloc (split): this instance shows that our spec chooses the best
                           fit block, even if it results in splitting.
- Heap overflow: this instance shows that mallocing a size greater than 7
                 results in a heap overflow (unsat).

Free:

We tested our free model on instances that we expected to be both SAT and UNSAT. The UNSAT tests include tests to ensure that if no free blocks exist (meaning that no one block can be freed as all are allocated) then our model returns UNSAT, and tests that ensure that the model returns UNSAT if freeing is possible but results in an invalid state. We tested that our model is SAT on valid instances where coalescing is needed and cases where it isn't. To ensure that our model behaves correctly on instances where coalescing is not needed, we tested an instance where there is only one allocated block that is then freed. On the other hand, to ensure that our model behaves correctly on instances where coalescing is needed, we tested that coalescing works correctly if coalescing needs to be done with a free block and its previous block, a freed block and its next block, and a block and both its previous and next blocks. We also ensured that coalescing results in valid states. In addition, we tested that our model returns UNSAT in case of heap overflow, which in our case occurs if HeapSize > 7.

Realloc:

- test0: if the size requested to realloc the block to is the same as the original size, 
	we should see that all states are the same
- test1: requesting a size of zero is the same as freeing the block
- test2: this instance frees like in the previous one, but includes coalescing
- test3: requesting a smaller size to realloc causes the block to split
- test4: if no free blocks fit, and the size requested is larger than the original
	block, we add the block to the end and replace the previous size of memory
	with a free block
- test5: the best fit block is exactly the requested size, so we follow a similar routine 	as malloc and replace the previous block with a free block
- test6: similar to the last instance, but tests the case where the best fit block
	is larger than needed, so we split
- test7: similar to test6, but shows that the split block becomes the old allocated
	block (to model copying of memory) and a new free block... is unsat because it
	uses the old block in the wrong place
- test8: unsatisfying when the blocks are not coalesced 



REACH GOAL/EXTENSIONS:

	Our primary reach goal was to model the three memory allocation algorithms using an "explicit free list." In our target goal, using an implicit free list meant that we find best-fit free blocks for malloc and realloc depending on their allocated tag (0 or 1). To model an explicit free list, we add the fields flist, flist_next, flist_prev, to our State sig. By doing this, we explicitly distinguish a list of unallocated cells that we are able to allocate memory into. In C programming, using an explicit free list has implications on the runtimes of the memory allocation functions, because searching for best-fit blocks requires looping only through the free list using its own next and previous pointers rather than going through every block in the heap. 
	On the subject of looping through the list, another reach goal we considered implementing (but didn't get to due to time constraints) that could act as a further extension of the model would be a first-fit implementation of malloc in which we explicitly model the process of looping through the free list. Our best-fit implementation makes the loop somewhat implicit, as it makes a set of blocks that are appropriately sized and then chooses the least large-enough block (which is our "best fit").
	A final extension of the reach goal which we included in our reach specs has to do with the inductive bounds of our model. We built these specs under the assumption that they would work alongside each other, meaning that a call to any function produces a valid final state that can act as StateA to one of the other functions. However, upon final inspection, we realized that the set of final states for malloc actually is larger than the set of instances that can satisfy the initial state constraints of the other functions, although they follow the same validState constraints. This issue arises in situations when free or realloc needs an allocated cell in the initial state to perform the function on. However, there are valid state transitions in malloc in which there are no allocated cells in the final state. To extend our model to actually satisfy a strong inductive hypothesis (that a valid final state from each function could act as a valid initial state for another function), we extended the free and realloc specs such that there is a "lone" HeapCell toFree or toRealloc, which would mimic the case of an invalid pointer or a NULL pointer being passed in to the function call, allowing all valid final states of malloc to be in the set of valid initial states for the other functions.
	NOTE: Due to time constraints, we have only implemented the explicit free list reach goal for malloc (in the malloc_reach spec) and free (in the free_reach spec). The free_reach spec includes what was mentioned in the discussion of strengthening the inductive invariant of the model. Implementing this in the realloc model would mean adding conditions for no existing toRealloc block. This would take on the same form as performing the malloc constraints with StateB.size, and would take over the case in which the valid starting space does not have any allocated blocks available to realloc.



