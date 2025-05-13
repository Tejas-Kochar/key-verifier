// Key store that simply appends entries to an array with linear scans for all operations

public class KeyStore1 {
    static class Entry {
        Object key, value;

        public Entry(Object key, Object value) {
            this.key = key;
            this.value = value;
        }
    }

    Entry[] entries = new Entry[0];
    /*@
        model \seq a;
        represents a = \dl_array2seq(entries);
    */

    // uniqueness of keys
    /* @
        invariant (\forall int x;
                  0 <= x < a.length;
                        !(\exists int y;
                        0 <= y < a.length && y != x;
                        ((Entry)a[x]).key == ((Entry)a[y]).key)
                  );
    */

    /*@
        normal_behaviour
        requires entries != null;
        ensures (\forall int i;
                0 <= i < a.length;
                ((Entry)a[i]).key == key  ==>  \result == ((Entry)a[i]).value);

        ensures !(\exists int i;
                0 <= i < a.length;
                ((Entry)a[i]).key == key  <==>  \result == null);
        assignable \strictly_nothing;
    */
    /*@ nullable */ Object /*@ strictly_pure */ get(Object key) {
        Object res = null;
        int counter = 0;

        /*@
            loop_invariant 0 <= counter && (a.length == 0 || counter < a.length);
            loop_invariant res == null ==>
                                !(\exists int i;
                                0 <= i < counter;
                                ((Entry)a[i]).key == key);

            decreases entries.length - counter;
        */
        while (counter < entries.length) {
            if (key.equals(entries[counter].key)) {
                res = entries[counter].value;
            }
            counter++;
        }
        return res;
    }

    /*@

    */
    void put(Object key, Object value) {}

    void remove(Object key) {}
}


