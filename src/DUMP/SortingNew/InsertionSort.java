package DUMP.SortingNew;

public class InsertionSort {

    /*@ normal_behaviour
      @ requires a.length > 0;
      @ ensures (\forall int x; 0 <= x < a.length-1; a[x] <= a[x+1]);
      @*/
    void sort(int[] a) {
        /*@ loop_invariant 1 <= i <= a.length;
          @ loop_invariant (\forall int x; 0 <= x < i-1; a[x] <= a[x+1]);
          @ assignable a[*];
          @ decreases a.length - i;
          @*/
        for (int i = 1; i < a.length; i++) {
            shift(a, i);
        }
    }

    /*@ normal_behaviour
      @ requires 0 < a.length && 1 <= i < a.length;
      @ requires (\forall int x; 0 <= x < i-1; a[x] <= a[x+1]);
      @ ensures (\forall int x; 0 <= x < i; a[x] <= a[x+1]);
      @ assignable a[0..i+1];
      @*/
    void shift(int[] a, int i) {
        int key = a[i], j;
        /*@
          @ loop_invariant -1 <= j < i;
          @ loop_invariant (\forall int x; j+1 < x <= i; key < a[x]);
          @ loop_invariant (\forall int x; 0 <= x < j; a[x] <= a[x+1]);
          @ decreases j+1;
          @ assignable a[0..i+1];
          @*/
        for (j = i-1; j >= 0 && a[j] > a[j+1]; j --) {
            a[j+1] = a[j];
        }
        a[j+1] = key;
    }
}
