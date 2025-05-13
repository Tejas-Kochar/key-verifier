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
    /*@
        invariant (\forall int x;
                  0 <= x < entries.length;
                        !(\exists int y;
                        0 <= y < entries.length && y != x;
                        entries[x].key == entries[y].key)
                  );
    */

    /*@
        normal_behaviour
        ensures (\forall int i;
                0 <= i < entries.length;
                entries[i].key == key  ==>  \result == entries[i].value);
        assignable \strictly_nothing;

        also

        normal_behavior
        ensures !(\exists int i;
                0 <= i < entries.length;
                entries[i].key == key  <==>  \result == null);
        assignable \strictly_nothing;
    */
    /*@ nullable */ Object /*@ pure */ get(Object key) {
        Object res = null;
        int counter = 0;

        /*@
            loop_invariant res == null ==>
                                !(\exists int i;
                                0 <= i <= counter;
                                entries[i].key == key);
            loop_invariant (\forall int i;
                            0 <= i <= counter;
                            entries[i].key == key  ==>  res == entries[i].value);
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
