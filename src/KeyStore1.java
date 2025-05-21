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
        model \map m;
        represents a = \dl_array2seq(entries);
    */

    /*@
        ensures
            entries != null && entries.length == 0;
    */
    KeyStore1() {
        entries = new Entry[0];
    }

    // uniqueness of keys
    /*@
        invariant (\forall int x;
                  0 <= x < a.length;
                        !(\exists int y;
                        x < y < a.length;
                        ((Entry)a[x]).key == ((Entry)a[y]).key)
                  );
    */
    // non-null (should be by default...)
    /*@
        invariant
            (\forall int i;
            0 <= i < entries.length;
            entries[i] != null && entries[i].key != null && entries[i].value != null);
    */

    // constraint yet to add to get - nothing changes. Should be easily provable considering no writing allowed anywhere
    /*@
        normal_behaviour
        requires entries != null;
        requires (\exists int i;
                0 <= i < a.length;
                ((Entry)a[i]).key == key);
        ensures (\exists int i;
                0 <= i < a.length;
                ((Entry)a[i]).key == key && \result == ((Entry)a[i]).value);
        ensures
            \old(a) == a;
        assignable \strictly_nothing;

        also

        requires !(\exists int i;
                0 <= i < a.length;
                ((Entry)a[i]).key == key);
        ensures \result == null;
        ensures
            \old(a) == a;
        assignable \strictly_nothing;
    */
    /*@ nullable */ Object /*@ strictly_pure */ get(Object key) {
        Object res = null;
        int counter = 0;

        /*@
            loop_invariant 0 <= counter <= a.length;
            loop_invariant res == null ==>
                                (\forall int i;
                                0 <= i < counter;
                                ((Entry)a[i]).key != key);

             loop_invariant res != null ==>
                              (\exists int i;
                              0 <= i < counter;
                              ((Entry)a[i]).key == key && res == ((Entry)a[i]).value);
            assignable \strictly_nothing;
            decreases a.length - counter;
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
        normal_behaviour
        requires
            get(key) == null;
        ensures
            get(key) == value;
        ensures
            a[0..a.length-1] == \old(a);

        also

        normal_behaviour
        requires
            get(key) != null;
        ensures
            get(key) == value;
        ensures
            (\forall int i;
            0 <= i < a.length;
            ((Entry)a[i]).key != key ==> a[i] == \old(a[i]));
    */
    void put(Object key, Object value) {
        if (get(key) == null) {
            Entry[] ne = new Entry[entries.length + 1];

            int counter = 0;

            /*@
                loop_invariant
                    0 <= counter <= a.length;
                loop_invariant
                    (\forall int i;
                    0 <= i < counter;
                    entries[i] == ne[i]);
                decreasing
                    a.length - counter;
                assignable
                    ne[0..ne.length-1];
            */
            while (counter < entries.length) {
                ne[counter] = entries[counter];
            }

            ne[counter] = new Entry(key, value);

            entries = ne;
        }
        else {
            int counter = 0;
            //@ ghost int ind;
            //@ set ind = -1;

//            i != ind ==> entries[i] == \old(entries[i]));
            /*@
                loop_invariant
                    0 <= counter <= a.length;
                loop_invariant
                    (\forall int i;
                    0 <= i < counter;
                    ((Entry)\old(a[i])).key != key  ==>  \old(a[i]) == a[i]);
                loop_invariant
                    (\forall int i;
                    0 <= i < counter;
                    ((Entry)\old(a[i])).key == key  ==>  entries[i].value == value);
                decreasing
                    a.length - counter;
                assignable
                    entries[*];
            */
            while (counter < entries.length) {
                if (key.equals(entries[counter].key)) {
                    //@ set ind = counter;
                    entries[counter].value = value;
                }
            }
        }
    }

    void remove(Object key) {}

    /* @
        model boolean indexOf(Object key) {
            \if
                a.length > 0
            \then

            return (\exists int i;
                    0 <= i < a.length;
                    ((Entry)a[i]).key == key);
        }
     */

    /*@
        normal_behaviour
        requires entries != null;
        ensures \result == (a.length > 0 && (\exists int i;
                            0 <= i < a.length;
                            ((Entry)a[i]).key == key));
        assignable \strictly_nothing;
    */
    boolean /*@ strictly_pure */ contains1(Object key) {
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


