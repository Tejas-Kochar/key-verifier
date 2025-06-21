package DUMP.Sorting;

class MInsertionSort {
    public int[] a;

    /*@
        model \seq seqa;
        represents seqa = \dl_array2seq(a);
     */

    /*@
        normal_behaviour
        requires a.length > 0 && 1 <= i < a.length;
        requires (\forall int x; 0 <= x < i-1; a[x] <= a[x]+1);
        requires (\forall int x, y; 0 <= x < y < i; a[x] <= a[y]);
        ensures 0 <= \result <= i;
        ensures (\forall int x; 0 <= x < \result; a[x] <= a[i]);
        ensures (\forall int x; \result < x < i; a[i] <= a[x]);
        assignable \nothing;
     */
    int /*@pure*/ findPosition(int i) {
        /*@
            maintaining -1 <= pos < i;
//            maintaining (\forall int x; pos < x < i; a[x] <= a[i]);
            maintaining pos < i-1 ==> a[pos+1] > a[i];
            maintaining (\forall int x; pos+1 < x < i; a[pos+1] <= a[x]);
            decreases pos+1;
            assignable \nothing;
         */
        for (int pos = i-1; pos >= 0 && a[pos] > a[i]; pos --)
            if (a[pos] <= a[i])
                return pos+1;
        return 0;
    }

    /*@
        normal_behaviour
        requires 0 < a.length && 1 <= i < a.length;
        requires (\forall int x; 0 <= x < i-1; a[x] <= a[x+1]);

        requires 0 <= pos <= i;
        requires (\forall int x; 0 <= x < pos; a[x] <= a[i]);
        requires (\forall int x; pos < x < i; a[i] <= a[x]);

        ensures seqa[0..pos] == \old(seqa[0..pos]);
        ensures seqa[pos+1..i+1] == \old(seqa[pos..i]);
        ensures seqa[pos] == \old(seqa[i]);

        ensures \dl_seqPerm(seqa, \old(seqa));
        ensures (\forall int x; 0 <= x < i; a[x] <= a[x+1]);
        assignable a[0..i+1];
     */
    void shiftv2(int i, int pos) {
        int key = a[pos];

        for (int j = i-1; j >= pos; j--) {
            a[j+1] = a[j];
        }
        a[pos] = key;
    }

    /*@
            normal_behaviour
            requires a.length > 0;
            ensures \dl_seqPerm(seqa, \old(seqa));
            ensures (\forall int x; 0 <= x < a.length-1; a[x] <= a[x+1]);
         */
    void sort() {
        /*@
            loop_invariant 1 <= i <= a.length;
            loop_invariant \dl_seqPerm(seqa, \old(seqa));
            loop_invariant (\forall int x; 0 <= x < i-1; a[x] <= a[x+1]);
            assignable a[*];
            decreases a.length - i;
         */
        for (int i = 1; i < a.length; i++) {
            shiftv2(i, findPosition(i));
        }
    }
}
