/* from key textbook, slightly modified */

package Sorting;

class Sort {
  public int[] a;

  /*@ model \seq seqa;
    @ represents seqa = \dl_array2seq(a);
    @*/
    
  /*@ public normal_behavior
    @ requires a.length > 0 && 0<= start && start < a.length; 
    @ ensures (\forall int i;start<=i && i<a.length; a[\result] >= a[i]);
    @ ensures start <= \result && \result < a.length;
    @*/
  int /*@ strictly_pure @*/ max(int start) {
    int counter = start; 
    int idx = start;
    /*@ loop_invariant  start<=counter && counter<=a.length &&
      @   start<=idx && idx<a.length  && start<a.length &&
      @   (\forall int x; x>=start && x<counter; a[idx]>=a[x]);
      @ assignable \strictly_nothing;
      @ decreases a.length - counter; 
      @*/
    while (counter<a.length) {
      if (a[counter] > a[idx]) 
        idx=counter; 
      counter=counter+1;
    }
    return idx;
  }

  /*@ public normal_behavior
    @ requires a.length > 0; 
    @ ensures  \dl_seqPerm(seqa,\old(seqa));
    @ ensures (\forall int x; 0 <= x < a.length-1; a[x] >= a[x+1]);
    @*/ 
  void sort() {
    int pos = 0; 
    int idx = 0;
    /*@ loop_invariant 0<=pos && pos<=a.length && 0<=idx && idx<a.length 
      @   && \dl_seqPerm(seqa,\old(seqa));
      @ loop_invariant (\forall int x; 0 <= x < pos-1; a[x] >= a[x+1]);
      @ assignable a[*];
      @ decreases a.length - pos; 
      @*/
    while (pos < a.length-1) {
      idx = max(pos);
      // swap(pos, idx);
      int tmp = a[idx];
      a[idx] = a[pos];
      a[pos] = tmp;
      pos = pos+1;
    } 
  }

  /*@ normal_behaviour
        requires 0 <= i < a.length && 0 <= j < a.length;
        ensures \dl_seqPerm(seqa, \old(seqa));
        assignable a[i], a[j];
     */
  void swap(int i, int j) {
    int temp = a[i];
    a[i] = a[j];
    a[j] = temp;
  }
}

