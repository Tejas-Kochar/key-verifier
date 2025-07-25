package DUMP.SortingNew;

public class SwapInsertionSortPerm {

    /*@ normal_behaviour
      @ requires a.length > 0;
      @ ensures \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
      @*/
    void sort(int[] a) {
        /*@ loop_invariant 1 <= i <= a.length;
          @ loop_invariant \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
          @ assignable a[*];
          @ decreases a.length - i;
          @*/
        for (int i = 1; i < a.length; i++) {
            shift(a, i);
        }
    }

    /*@ normal_behaviour
      @ requires 0 < a.length && 1 <= i < a.length;
      @ ensures \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
      @ assignable a[0..i+1];
      @*/
    void shift(int[] a, int i) {
        /*@
          @ loop_invariant -1 <= j < i;
          @ loop_invariant \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
          @ decreases j+1;
          @ assignable a[0..i+1];
          @*/
        for (int j = i-1; j >= 0 && a[j] > a[j+1]; j --) {
            swap(a, j, j+1);
        }
    }

    /*@ normal_behaviour
      @ requires 0 <= j < a.length && 0 <= j1 < a.length;
      @ ensures \old(a[j]) == a[j1] && \old(a[j1]) == a[j];
      @ ensures \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
      @ assignable a[j], a[j1];
      @*/
    void swap(int[] a, int j, int j1) {
        int tmp = a[j];
        a[j] = a[j1];
        a[j1] = tmp;
    }
}
