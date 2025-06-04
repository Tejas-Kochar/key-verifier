package Sorting;

public class InsertionSort {
    int[] a;

    /*@
        model \seq seqa;
        represents seqa = \dl_array2seq(a);
     */
    /*@
        public normal_behaviour
        requires a.length > 0;
        ensures \dl_seqPerm(seqa, \old(seqa));
        ensures (\forall int x, y; 0 <= x < a.length && 0 <= y < a.length; x < y ==> a[x] <= a[y]);
     */
    void sort() {
        /*@
            loop_invariant 1 <= i <= a.length;
            loop_invariant \dl_seqPerm(seqa, \old(seqa));
            loop_invariant (\forall int x; 0 <= x < i-1; a[x] <= a[i]);
            assignable a[*];
            decreases a.length - i;
         */
        for (int i = 1; i < a.length; i++) {
            int key = a[i];
            int j = i - 1;

            /*@
                loop_invariant -1 <= j <= i-1;
                // values after i should not have changed
                loop_invariant (\forall int x; i < x < a.length; a[x] == \old(a[x]));
                // values before j have not changed (strictly before old j, before and equal new j)
                loop_invariant (\forall int x; 0 <= x <= j; a[x] == \old(a[x])); // assuming j is the new j
                loop_invariant (\forall int x; j <= x < i; key < a[x]);
                loop_invariant (\forall int x; j + 1 <= x < i; \old(a[x]) == a[x+1]); // values at and after old j shifted one to the right
                assignable a[0..i];
                decreases j + 1;
             */
            while (j >= 0 && a[j] > key) {
                a[j + 1] = a[j];
                j = j - 1;
            }
            a[j + 1] = key;
        }
    }
}
