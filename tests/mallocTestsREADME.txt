The following are cases tested in our malloc spec:
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
