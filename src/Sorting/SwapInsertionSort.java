package Sorting;

public class SwapInsertionSort {
    public int[] a;

    /*@
        model \seq seqa;
        represents seqa = \dl_array2seq(a);
     */



    /*@
        public normal_behaviour
        requires a.length > 0;
//        ensures \dl_seqPerm(seqa, \old(seqa));
        ensures (\forall int x; 0 <= x < a.length-1; a[x] <= a[x+1]);
     */
    void sort() {
        /*@
            loop_invariant 1 <= i <= a.length;
//            loop_invariant \dl_seqPerm(seqa, \old(seqa));
            loop_invariant (\forall int x; 0 <= x < i-1; a[x] <= a[x+1]);
            assignable a[*];
            decreases a.length - i;
         */
        for (int i = 1; i < a.length; i++) {
            shift(i);
        }
    }

    /*@
        public normal_behaviour
        requires 1 <= i < a.length && a.length > 0;
        requires (\forall int x, y; 0 <= x < i && 0 <= y < i; x < y ==> a[x] <= a[y]);
//        ensures \dl_seqPerm(seqa, \old(seqa));
        ensures (\forall int x; 0 <= x < i; a[x] <= a[x+1]);
        assignable a[0..i+1];
     */
    void shift(int i) {
        /*@
            loop_invariant -1 <= j < i;
//            loop_invariant \dl_seqPerm(\dl_array2seq(a), \dl_array2seq(\old(a)));
            loop_invariant (\forall int x; j+1 <= x < i; a[x] <= a[x+1]);
            decreases j+1;
            assignable a[0..i+1];
         */
        for (int j = i-1; j >= 0 && a[j] > a[j+1]; j --) {
            int tmp = a[j+1];
            a[j+1] = a[j];
            a[j] = tmp;
        }
    }
}




