package DUMP.Sorting;

public class CInsertionSort {
    int[] a;

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
            loop_invariant 1 <= i && i <= a.length;
//            loop_invariant \dl_seqPerm(seqa, \old(seqa));
            loop_invariant (\forall int x; 0 <= x < i-1; a[x] <= a[x+1]);
            loop_invariant (\forall int k; 0 <= k < i-1; a[k] <= a[i-1]);
            assignable a[*];
            decreases a.length - i;
         */
        for (int i = 1; i < a.length; i++) {
            int key = a[i];
            int j = i - 1;
            /*@
                loop_invariant -1 <= j && j <= i-1;
//                loop_invariant (\forall int k; j <= k < i; a[k] >= key); // wrong not valid initially
//                loop_invariant (\forall int k; i+1 <= k < a.length; a[k] == \old(a[k]));
                loop_invariant (\forall int x; 0 <= x < i-1; a[x] <= a[x+1]);
//                loop_invariant \dl_seqPerm(seqa, \old(seqa));
                assignable a[0..i+1];
                decreases j + 1;
             */
            while (j >= 0 && a[j] > key) {
                a[j + 1] = a[j];
                j = j - 1;
            }
            a[j + 1] = key;
//            //@ assert \dl_seqPerm(seqa, \old(seqa);
        }
    }
}
