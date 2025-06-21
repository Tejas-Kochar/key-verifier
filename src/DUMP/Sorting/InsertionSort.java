package DUMP.Sorting;

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
            loop_invariant (\forall int x, y; 0 <= x < i && 0 <= y < i; x < y ==> a[x] < a[y]);
            assignable a[*];
            decreases a.length - i;
         */
        for (int i = 1; i < a.length; i++) {
            int key = a[i];
            int j = i - 1;

            int jc = shift(key, i);

            // @ assert \dl_seqPerm(\seq_concat(seqa[0..jc+1], seqa[jc+2..i+1]), \old(seqa[0..i]));
//            a[jc + 1] = key;
        }
    }

    /*@
        requires 0 < i < a.length && a.length > 0;
        requires a[i] == key;
        // segment < i is sorted
        requires (\forall int x, y; 0 <= x < i && 0 <= y < i; x < y ==> a[x] < a[y]);

        // makes sure that segment <= i is sorted
        ensures (\forall int x, y; 0 <= x <= i && 0 <= y <= i; x < y ==> a[x] < a[y]);
        ensures \dl_seqPerm(seqa, \old(seqa));

        // shifted segment is larger than key
        ensures (\forall int x; \result < x < i; key < a[x]);
        // shifted segment is actually just shifted
        ensures (\forall int x; \result < x < i; \old(a[x]) == a[x+1]);
        // segment before and including result is unchanged
        ensures (\forall int x; 0 <= x <= \result; \old(a[x]) == a[x]);

        // shift should now also ensure output is permutation of input
//        ensures \dl_seqPerm(seqa, \old(seqa)); // cannot prove this it seems
        // ensures \dl_seqPerm(seqa[(\result+1)..i], \old(seqa[(\result+1)..i]));

        ensures (\forall int x; i < x < a.length; \old(a[x]) == a[x]);
        assignable a[0..i+1]; // remaining part after i cannot have been changed. Also stated explicitly as ensures above
     */
    private int shift(final int key, final int i) {
        int j = i -  1;

        /*@
            loop_invariant -1 <= j <= i-1;

            // values after i should not have changed
            loop_invariant (\forall int x; i < x < a.length; a[x] == \old(a[x]));
            // values before j have not changed (strictly before old j, before and equal new j)
            loop_invariant (\forall int x; 0 <= x <= j; a[x] == \old(a[x])); // assuming j is the new j
            // shifted segment is larger than key
            loop_invariant (\forall int x; j < x < i; key < a[x]);
            // shifted segment is asctually shifted
            loop_invariant (\forall int x; j < x < i; \old(a[x]) == a[x+1]); // values at and after old j shifted one to the right
            assignable a[0..i];
            decreases j + 1;
         */
        while (j >= 0 && a[j] > key) {
            a[j + 1] = a[j];
            a[j] = key; // modified version in which array is a permutation after each iteration
            j = j - 1;
        }
//        a[j + 1] = key;
        return j;
    }
}
