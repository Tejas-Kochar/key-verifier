package DUMP.Keystores;// Key store that simply appends entries to an array with linear scans for all operations

public class KeyStore1 {
    static class Entry {
        final Object key;
        Object value;

        // @ public model \locset fp;
        // @ represents fp = key, value;

        public Entry(Object key, Object value) {
            this.key = key;
            this.value = value;
        }

//        /* @
//            ensures \result == (\typeof(o) == )
//        */
//        public boolean /* @pure*/ equals(Object o) {
//            if (this == o) return true;
//            if (o == null || getClass() != o.getClass()) return false;
//
//            Entry entry = (Entry) o;
//            return key.equals(entry.key) && value.equals(entry.value);
//        }
    }

    private /*@nullable@*/ Entry[] entries = new Entry[10];
    private int size;

    // @ public model \locset footprint;
    // @ public accessible \inv: footprint;
    // @ public accessible footprint: footprint;

    // @ private represents footprint = entries, entries[*].fp, size;

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
        ensures size == 0;
    */
    public /*@pure@*/ KeyStore1() {
        entries = new Entry[0];
    }

    /*@ public normal_behaviour
       ensures \result == (size > 0 && (\exists int i; 0 <= i && i < size; entries[i].key == o));
    */
    public boolean /*@pure*/ contains(Object o) {
        /*@ loop_invariant 0 <= i && i <= size
          @  && (\forall int x; 0 <= x && x < i; entries[x].key != o);
          @ assignable \nothing;
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            if(entries[i].key == o) {
                return true;
            }
        }
        return false;
    }

    /*@ private normal_behaviour
        requires 0 <= from <= size;
        ensures \result == (size > 0 && (\exists int i; from <= i && i < size; entries[i].key == o));
        measured_by size - from;
     */
    private /*@pure@*/ boolean containsRec(final Object o, int from) {
        if (from == size)
            return false;
        else if (entries[from].key == o)
            return true;
        else
            return containsRec(o, from + 1);
    }

    /*@
        public normal_behaviour
        requires contains(key);
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
            if(entries[i].key == key) {
                return entries[i].value;
            }
        }
        return null;
    }

    /*@ normal_behavior
      @   assignable entries;
      @   ensures \fresh(entries);
      @   ensures entries.length > \old(entries.length);
      @   ensures (\forall int x; 0 <= x && x < size; entries[x] == \old(entries[x]));
      @*/
    private void enlarge() {
        final Entry[] newArray = new Entry[entries.length == 0 ? 10 : entries.length*2];

        /*@ loop_invariant 0 <= i && i <= size
          @  && (\forall int x; 0 <= x && x < i; newArray[x] == entries[x]);
          @ assignable newArray[*];
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            newArray[i] = entries[i];
        }
        entries = newArray;
        // @ set footprint = \set_union(\all_fields(this), \all_fields(array));
    }

    /*@
        public normal_behaviour
        requires !contains(key);
        ensures get(key) == value;
        ensures (\forall int x; 0 <= x < size - 1; entries[x] == \old(entries[x]));
        ensures size == \old(size) + 1;

        also

        public normal_behaviour
        requires contains(key);
        ensures get(key) == value;
        ensures size == \old(size);
        ensures (\forall int i; 0 <= i < size;
            entries[i].key != key ==> entries[i] == \old(entries[i]));
    */
    public void put(Object key, Object value) {
        if (!contains(key)) {
            if (size == entries.length) {
//                Entry[] ne = new Entry[entries.length * 2];
//
//                /*@
//                    loop_invariant 0 <= i <= size;
//                    loop_invariant (\forall int j; 0 <= j < i; entries[j] == ne[j]);
//                    decreasing size - i;
//                    assignable ne[0..size];
//                */
//                for (int i = 0; i < size; i++) {
//                    ne[i] = entries[i];
//                }
//
//                entries = ne;
                enlarge();
            }

            entries[size++] = new Entry(key, value);
        }
        else {
            //@ ghost int ind;
            //@ set ind = -1;

//            i != ind ==> entries[i] == \old(entries[i]));
            for (int i = 0; i < size; i++) {
            /*@
                loop_invariant 0 <= i <= size;
                loop_invariant (\forall int x; 0 <= x < i;
                    entries[x].key != key ==> (entries[x] == \old(entries[x]) &&
                                              entries[x].key == \old(entries[x].key) &&
                                              entries[x].value == \old(entries[x].value)));
                loop_invariant (\forall int x; 0 <= x < i;
                    \old(entries[x].key) == key  ==>  (entries[x].value == value && entries[x].key == key));
                decreasing size - i;
                assignable entries[*];
            */
                if (entries[i].key == key) {
                    entries[i].value = value;
                    break;
                }
            }
        }
    }

    /* @
        ensures contains(key) ==>
                    (size == \old(size) && get(key) == value
                    && (\forall int x; 0 <= x < size;
                    \old(entries[x].key) != key ==> \old(entries[x]) == entries[x]

    @*/
    public void putV2(Object key, Object value) {
        for (int i = 0; i < size; i++) {
            if (entries[i].key == key) {
                entries[i].value = value;
                return;
            }
        }

        if (size == entries.length) {
            enlarge();
        }

        entries[size++] = new Entry(key, value);
    }

    /*@
        public normal_behaviour
        ensures !contains(key);
        ensures (\forall int x; 0 <= x < size;
     */
    public void remove(Object key) {}
}


