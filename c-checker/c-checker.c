#include <assert.h>
#include <ctype.h>
#include <fcntl.h> 
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h> 
#include <sys/stat.h> 
#include <sys/types.h> 
#include <unistd.h>

inline int next_int(char **s) {
  while (isspace(**s)) (*s)++;
  int sign;
  if (**s == '-') {
    sign = -1;
    (*s)++;
  } else sign = 1;
  int i = 0;
  while (!isspace(**s)) i = 10*i + *(*s)++ - '0';
//  printf("read %d\n",sign*i);
  return sign*i;
}

inline void adjust(int nElems, int* mElems, int** elems) {
  while (nElems >= *mElems) {
    if (*mElems) *mElems <<= 1; else *mElems = 1;
//    printf("Increased store size to %d\n",*mElems);
    *elems = realloc(*elems,sizeof(int)**mElems);
  }
}

inline int computeIndex(int lit) {
  return lit > 0 ? 2*lit-1 : -2*lit;
}

inline int countFree(int nFrees, int* frees, int* block) {
  int count = 0;
  for (int size = 1; size <= nFrees; size++) {
    int c = frees[size-1];
    while (c) {
      count += size+1;
      c = block[c];
    }
  }
  return count;
}

int checkRUP(int c, int d, int* nBlock, int* mBlock, int** block, int* nAssignment, int** assignment) {
  int entailed = 0;
  assert(d);
  int dLit;
  while ((dLit = (*block)[d])) {
//    printf("Checking literal %d\n", dLit);
    int index = computeIndex(dLit);
//    printf("index = %d\n",index);
    if (index > *nAssignment) {
      *assignment = realloc(*assignment,sizeof(int)*index);
//      printf("Zeroing ...\n");
      memset(*assignment+*nAssignment,0,(index-*nAssignment)*sizeof(int));
      *nAssignment = index;
    }
    if (!((*assignment)[index-1])) {
      entailed++;
      (*block)[(*nBlock)++] = -dLit;
      adjust(*nBlock, mBlock, block);
      (*block)[*nBlock] = 0;
      int newIndex = computeIndex(-dLit);
      if (newIndex > *nAssignment) {
        *assignment = realloc(*assignment,sizeof(int)*newIndex);
//        printf("Zeroing 2 ...\n");
        memset(*assignment+*nAssignment,0,(newIndex-*nAssignment)*sizeof(int));
        *nAssignment = newIndex;
      }
      (*assignment)[newIndex-1] = 1;
//      printf("checked index %d which was at %d and now adding index %d to false list and was set to %d\n",index,(*assignment)[index-1],computeIndex(-dLit),(*assignment)[computeIndex(-dLit)-1]);
    }
    d++;
  }
//  printf("entailed = %d\n",entailed);
  return entailed;
}

int main (int argc, char** argv) {
  int fd = open(argv[1], O_RDONLY);
  struct stat fd_info;
  fstat(fd, &fd_info);
  off_t length = fd_info.st_size;
  char* input = mmap(NULL, length, PROT_READ, MAP_PRIVATE, fd, 0);
  char* bInput = input;
  char* eInput = input+length-1;
  int nBlock = 1;
  int mBlock = 1;
  int* block = NULL;
  int nClauses = 0;
  int mClauses = 0;
  int* clauses = NULL;
  int nStack = 0;
  int mStack = 0;
  int* stack = NULL;
  int refuted = 0;
  int nFrees = 0;
  int* frees = NULL;
  int nAssignment = 0;
  int* assignment = NULL;
  int dummy = 0;
  while (input < eInput) {
//    if ((dummy++ % 1000) == 0) printf("block = %d, clauses = %d, stack = %d, frees = %d, assignment = %d, reclaimable = %d\n",mBlock,mClauses,mStack,nFrees,nAssignment,countFree(nFrees,frees,block));
    int cid = next_int(&input);
    if (cid) {
//      printf("trying to add %d\n",cid);
      int c = nBlock;
      int final_c;
      int next;
      do {
        next = next_int(&input);
        adjust(nBlock, &mBlock, &block);
        block[nBlock++] = next;
      } while (next);
      int cLength = nBlock-c-1;
      if (cLength && cLength <= nFrees && frees[cLength-1]) {
//        printf("reuse\n");
        final_c = frees[cLength-1];
//        printf("%d %d %d\n",cLength-1,frees[cLength-1],block[frees[cLength-1]]);
        frees[cLength-1] = block[frees[cLength-1]];
        memcpy(block+final_c,block+c,sizeof(int)*(cLength+1));
      } else final_c = c;
//      printf("adjusting clauses\n");
      adjust(nClauses, &mClauses, &clauses);
      while (cid > nClauses+1) {
        clauses[nClauses++] = 0;
        adjust(nClauses, &mClauses, &clauses);
      }
      int id = next_int(&input);
      if (id) {
        int f = c;
        int literal;
//        printf("Starting with empty assignment ...\n");
        while ((literal = block[f++])) {
//          printf("Assigning %d to false ...\n",literal);
          int index = computeIndex(literal);
          if (index > nAssignment) {
            assignment = realloc(assignment,sizeof(int)*index);
            memset(assignment+nAssignment,0,(index-nAssignment)*sizeof(int));
            nAssignment = index;
          }
          assignment[index-1] = 1;
        }
        // start with negated clause
        clauses[nClauses] = 0; // to be safe
//        printf("Checking RUP\n");
        while (id) {
          adjust(nStack, &mStack, &stack);
          stack[nStack++] = id;
          id = next_int(&input);
        }
        int oBlock = nBlock-1;
        nBlock = oBlock; // save propagated literals after new clause
        int i = 0;
        while (i < nStack) {
          id = stack[i++];
//          printf("Propagating with %d\n", id);
          int entailed = checkRUP(c, clauses[id-1], &nBlock, &mBlock, &block, &nAssignment, &assignment);
          if (entailed) {
            assert(entailed == 1);
          } else {
            clauses[nClauses++] = final_c;
//            printf("added redundant clause %d with %d literal(s) at %d\n",nClauses,cLength,final_c);
//            printf("%d\n",block[clauses[nClauses-1]]);
            if (!cLength) { // empty clause
              refuted = 1;
            }
            nStack = 0;
            break;
          }
        }
        block[oBlock] = 0;
        f = c;
        while ((literal = block[f++])) {
          int index = computeIndex(literal);
//          printf("Resetting %d ...\n",literal);
          assignment[index-1] = 0;
        }
        if (final_c == c) nBlock = oBlock+1; else nBlock = c;
      } else {
        clauses[nClauses++] = final_c;
//        printf("added clause %d with %d literal(s) at %d\n",nClauses,cLength,final_c);
      }
    } else {
      while (1) {
        int id = next_int(&input);
        if (!id) break;
        int c = clauses[id-1];
//        printf("was stored at %d\n",c);
        assert(c);
        clauses[id-1] = 0;
//        printf("deleted clause %d\n", id);
        int size = 0;
        while (block[c+size]) size++;
//        printf("size was %d\n", size);
        if (size > nFrees) {
          frees = realloc(frees,sizeof(int)*size);
          memset(frees+nFrees,0,(size-nFrees)*sizeof(int));
          nFrees = size;
        }
        int d = frees[size-1];
        frees[size-1] = c;
//        printf("reusing %d\n",c);
        block[c] = d;
      }
    }
  }
  assert(refuted);
  munmap(bInput,length);
  close(fd);
  if (stack) free(stack);
  if (clauses) free(clauses);
  if (block) free(block);
  if (frees) free(frees);
  printf("SUCCESS\n");
  exit(EXIT_SUCCESS);
}
