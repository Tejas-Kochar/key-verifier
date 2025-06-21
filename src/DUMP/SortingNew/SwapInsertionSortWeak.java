package DUMP.SortingNew;

public class SwapInsertionSortWeak {

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
        /*@
          @ loop_invariant -1 <= j < i;
          @ loop_invariant (\forall int x; j+1 <= x < i; a[x] <= a[x+1]);
//          @ loop_invariant (\forall int x; j+1 <= x < i+1; a[j+1] <= a[x]); // using this instead of one above did not change result
          @ loop_invariant (\forall int x; 0 <= x < j; a[x] <= a[x+1]);
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
      @ assignable a[j], a[j1];
      @*/
    void swap(int[] a, int j, int j1) {
        int tmp = a[j];
        a[j] = a[j1];
        a[j1] = tmp;
    }
}
