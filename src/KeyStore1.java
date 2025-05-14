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
                  0 <= x < a.length;
                        !(\exists int y;
                        x <= y < a.length;
                        ((Entry)a[x]).key == ((Entry)a[y]).key) ==> x == y
                  );
    */
    // non-null (should be by default...)
    /*@
        invariant
            (\forall int i;
            0 <= i < entries.length;
            entries[i] != null && entries[i].key != null && entries[i].value != null);
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

             loop_invariant (\forall int i;
                              0 <= i < counter;
                              ((Entry)a[i]).key == key  ==>  res == ((Entry)a[i]).value);
            assignable \strictly_nothing;
            decreases a.length - counter;
        */
        while (counter < entries.length) { // as of now, I think proof is not using uniquness part to show that forall holds
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

    /*@
        normal_behaviour
        requires entries != null;
        ensures \result == (a.length > 0 && (\exists int i;
                            0 <= i < a.length;
                            ((Entry)a[i]).key == key));
        assignable \strictly_nothing;
    */
    boolean /*@ strictly_pure */ contains(Object key) {
        int counter = 0;
        boolean res = false;
        /*@
            loop_invariant 0 <= counter && (a.length == 0 ==> counter == 0) && (a.length == 0 || counter < a.length);
            loop_invariant res == (counter > 0 && (\exists int i;
                            0 <= i < counter;
                            ((Entry)a[i]).key == key));

            assignable \strictly_nothing;
            decreases a.length - counter;
        */
        while (counter < entries.length) {
            if (key.equals(entries[counter].key)) {
                res = true;
            }
            counter++;
        }
        return res;
    }

    /*@
        normal_behaviour
        requires
            entries != null;
        ensures
            \result == !(\forall int i; 0 <= i < a.length; ((Entry)a[i]).key != key);
        assignable
            \strictly_nothing;
    */
    boolean /*@ strictly_pure */ contains2(Object key) {
        int counter = 0;
        /*@
            loop_invariant
                0 <= counter <= a.length;
            loop_invariant
                (\forall int i; 0 <= i < counter; ((Entry)a[i]).key != key);
            assignable \strictly_nothing;
            decreases a.length - counter;
        */
        while (counter < entries.length) {
            if (key.equals(entries[counter].key)) {
                return true;
            }
            counter++;
        }
        return false;
    }

    /*@
        normal_behaviour
        requires
            entries != null;
        ensures
            \result == !(\forall int i; 0 <= i < a.length; ((Entry)a[i]).key != key);
        assignable
            \strictly_nothing;
    */
    boolean /*@ strictly_pure */ contains3(Object key) {
        boolean res = false;
        int counter = 0;
        /*@
            loop_invariant
                0 <= counter <= a.length;
            loop_invariant
                res <==> (counter > 0 && (\forall int i; 0 <= i < counter; ((Entry)a[i]).key != key));
            assignable \strictly_nothing;
            decreases a.length - counter;
        */
        while (counter < entries.length) {
            if (key.equals(entries[counter].key)) {
                res = true;
            }
            counter++;
        }
        return res;
    }
}


