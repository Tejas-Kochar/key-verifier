package Sorting;

public class SwapInsertionSort {
    public int[] a;

    /*@
        model \seq seqa;
        represents seqa = \dl_array2seq(a);
     */



    /*@
        normal_behaviour
        requires a.length > 0;
        ensures \dl_seqPerm(seqa, \old(seqa));
        ensures (\forall int x, y; 0 <= x < a.length && 0 <= y < a.length; x < y ==> a[x] <= a[y]);
     */
    void sort() {
        /*@
            loop_invariant 1 <= i <= a.length;
            loop_invariant \dl_seqPerm(seqa, \old(seqa));
            loop_invariant (\forall int x, y; 0 <= x < i && 0 <= y < i; x < y ==> a[x] <= a[y]);
            assignable a[*];
            decreases a.length - i;
         */
        for (int i = 1; i < a.length; i++) {
            shift(i);
        }
    }

    /*@
        normal_behaviour
        requires 1 <= i < a.length && a.length > 0;
        requires (\forall int x, y; 0 <= x < i && 0 <= y < i; x < y ==> a[x] <= a[y]);
        ensures \dl_seqPerm(seqa, \old(seqa));
        ensures (\forall int x, y; 0 <= x <= i && 0 <= y <= i; x < y ==> a[x] <= a[y]);
        assignable a[0..i+1];
     */
    void shift(int i) {
        /*@
            loop_invariant -1 <= j < i;
            loop_invariant \dl_seqPerm(seqa, \old(seqa));
            loop_invariant (\forall int x, y; j+1 <= x <= i && j+1 <= y <= i; x < y ==> a[x] <= a[y]);
            decreases j+1;
            assignable a[0..i+1];
         */
        for (int j = i-1; j >= 0 && a[j] > a[j+1]; j --) {
            swap(j, j+1);
        }
    }

    /*@ normal_behaviour
        requires a.length == 2 && a[0] == 0 && a[1] == 1 && i != j && 0 <= i < a.length && 0 <= j < a.length;
//        ensures \dl_seqPerm(seqa, \old(seqa));
        ensures \dl_seqPerm(\dl_array2seq(a), \dl_array2seq(\old(a)));
        ensures \old(a) == a;
        ensures a[1] == 0 && a[0] == 1;
        assignable a[i], a[j];
     */
    void swap(int i, int j) {
        int temp = a[i];
        a[i] = a[j];
        a[j] = temp;
    }
//        requires a != null && 0 <= i < a.length && 0 <= j < a.length && a.length > 0 && i != j;
}




