// Key store that simply appends entries to an array with linear scans for all operations

public class KeyStore1 {
    static class Entry {
        Object key, value;

        //@ public model \locset fp;
        //@ represents fp = key, value;

        public Entry(Object key, Object value) {
            this.key = key;
            this.value = value;
        }

        public boolean equals(Object o) {
            if (this == o) return true;
//            if (o == null || getClass() != o.getClass()) return false;

            Entry entry = (Entry) o;
            return key.equals(entry.key) && value.equals(entry.value);
        }
    }

    private /*@nullable@*/ Entry[] entries = new Entry[10];
    private int size;

    //@ public model \locset footprint;
    //@ public accessible \inv: footprint;
    //@ public accessible footprint: footprint;

    //@ private represents footprint = entries, entries[*].fp, size;

    /*@
        private invariant entries != null;
        private invariant 0 <= size && size <= entries.length;
        private invariant (\forall int i; 0 <= i && i < size;
                            entries[i] != null && entries[i].key != null && entries[i].value != null);
    */

    // not sure why the next one is needed, so will try without it too
    /*@
        private invariant \typeof(entries) == \type(Entry[]);
     */


    // uniqueness of keys
    // if does not work, can try defining helper method to get key at index
    /*@
       private invariant (\forall int x, y; 0 <= x < size && 0 <= y < size && x != y;
                            entries[x].key != entries[y].key
                         );
    */




    /*@ public normal_behaviour
        ensures size == 0 && \fresh(footprint);
    */
    public /*@pure@*/ KeyStore1() {
        entries = new Entry[0];
    }

    /*@ public normal_behaviour
       accessible footprint;
       ensures \result == (\exists int i; 0 <= i && i < size; entries[i].key.equals(o));
    */
    public boolean /*@pure*/ contains(Object o) {
        /*@ loop_invariant 0 <= i && i <= size
          @  && (\forall int x; 0 <= x && x < i; !entries[x].key.equals(o));
          @ assignable \nothing;
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            if(entries[i].key.equals(o)) {
                return true;
            }
        }
        return false;
    }



    /*@
        public normal_behaviour
        requires contains(key);
        accessible footprint;
        ensures (\exists int i; 0 <= i < size;
                entries[i].key == key && \result == entries[i].value);
        ensures \old(size) == size;
        assignable \strictly_nothing;

        also

        public normal_behaviour
        requires !contains(key);
        ensures \result == null;
        ensures \old(size) == size;
        assignable \strictly_nothing;
    */
    public /*@nullable*/ Object /*@pure*/ get(Object key) {

        /*@
            loop_invariant 0 <= i <= size
                && (\forall int x; 0 <= x && x < i; entries[x].key != key);
            assignable \strictly_nothing;
            decreases size - i;
        */
        for (int i = 0; i < size; i++) {
            if(entries[i].key.equals(key)) {
                return entries[i].value;
            }
        }
        return null;
    }

    /* @
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

            /* @
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
            /* @
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
}


