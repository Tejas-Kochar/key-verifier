package KeyStore1_2;

public class KeyStore1_2 {
    static class Entry {
        final Object key;
        Object value;

        public Entry(Object key, Object value) {
            this.key = key;
            this.value = value;
        }
    }

    private /*@nullable@*/ Object[] keys = new Object[10];
    private /*@nullable@*/ Object[] values = new Object[10];
    
    private int size;

    /*@
        private invariant keys != null && values != null && keys != values;
        private invariant keys.length == values.length;
        private invariant 0 <= size && size <= keys.length;
        private invariant (\forall int i; 0 <= i && i < size;
                            keys[i] != null && values[i] != null);
    */


    // uniqueness of keys
    // if does not work, can try defining helper method to get key at index
    /*@
       private invariant (\forall int x, y; 0 <= x < size && 0 <= y < size && x != y;
                            keys[x] != keys[y]
                         );
    */

    // need to understand why this is needed
    /*@
        invariant \typeof(keys) == \type(Object[]) && \typeof(values) == \type(Object);
     */


    /*@ public normal_behaviour
        ensures size == 0;
    */
    public /*@pure@*/ KeyStore1_2() {
        keys = new Object[10];
        values = new Object[10];
    }

    /*@ public normal_behaviour
       ensures \result == (size > 0 && (\exists int i; 0 <= i && i < size; keys[i] == o));
    */
    public boolean /*@pure*/ contains(Object o) {
        /*@ loop_invariant 0 <= i && i <= size
          @  && (\forall int x; 0 <= x && x < i; keys[x] != o);
          @ assignable \nothing;
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            if(keys[i] == o) {
                return true;
            }
        }
        return false;
    }

    /*@ private normal_behaviour
        requires 0 <= from <= size;
        ensures \result == (size > 0 && (\exists int i; from <= i && i < size; keys[i] == o));
        measured_by size - from;
     */
    private /*@pure@*/ boolean containsRec(final Object o, int from) {
        if (from == size)
            return false;
        else if (keys[from] == o)
            return true;
        else
            return containsRec(o, from + 1);
    }

    /*@
        public normal_behaviour
        requires contains(key);
        ensures (\exists int i; 0 <= i < size;
                keys[i] == key && \result == values[i]);
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
                && (\forall int x; 0 <= x && x < i; keys[x] != key);
            assignable \strictly_nothing;
            decreases size - i;
        */
        for (int i = 0; i < size; i++) {
            if(keys[i] == key) {
                return values[i];
            }
        }
        return null;
    }

    /*@ normal_behavior
      @   assignable keys, values;
      @   ensures \fresh(keys) && \fresh(values);
      @   ensures keys.length > \old(keys.length);
      @   ensures (\forall int x; 0 <= x && x < size; keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
      @*/
    private void enlarge() {
        final Object[] newKeys = new Object[keys.length == 0 ? 10 : keys.length*2];
        final Object[] newValues = new Object[values.length == 0 ? 10 : values.length*2];

        /*@ loop_invariant 0 <= i && i <= size
          @  && (\forall int x; 0 <= x && x < i; newKeys[x] == \old(keys[x]) && newValues[x] == \old(values[x]));
          @ assignable newKeys[*], newValues[*];
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            newKeys[i] = keys[i];
            newValues[i] = values[i];
        }
        keys = newKeys;
        values = newValues;
    }

    /*@
        public normal_behaviour
        requires !contains(key);
        ensures get(key) == value;
        ensures (\forall int x; 0 <= x < size - 1; keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
        ensures size == \old(size) + 1;

        also

        public normal_behaviour
        requires contains(key);
        ensures get(key) == value;
        ensures size == \old(size);
        ensures (\forall int x; 0 <= x < size;
            keys[x] != key ==> keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
    */
    public void put(Object key, Object value) {
        if (!contains(key)) {
            if (size == keys.length) {
//                Entry[] ne = new Entry[keys.length * 2];
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

            keys[size] = key;
            values[size] = value;
            size ++;
        }
        else {
            for (int i = 0; i < size; i++) {
            /*@
                loop_invariant 0 <= i <= size;
                loop_invariant (\forall int x; 0 <= x < i;
                    keys[x] != key ==> keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
                loop_invariant (\forall int x; 0 <= x < i;
                    \old(keys[x]) == key  ==>  (values[x] == value && keys[x] == key));
                decreasing size - i;
                assignable keys[*], values[*];
            */
                if (keys[i] == key) {
                    values[i] = value;
                    break;
                }
            }
        }
    }

    /* @
        ensures contains(key) ==>
                    (size == \old(size) && get(key) == value
                    && (\forall int x; 0 <= x < size;
                    \old(keys[x]) != key ==> keys[x] == \old(keys[x]) && values[x] == \old(values[x])

    @*/
    public void putV2(Object key, Object value) {
        for (int i = 0; i < size; i++) {
            if (keys[i] == key) {
                values[i] = value;
                return;
            }
        }

        if (size == keys.length) {
            enlarge();
        }

        keys[size] = key;
        values[size] = value;
        size ++;
    }

    /* @
        public normal_behaviour
        ensures !contains(key);
        ensures (\forall int x; 0 <= x < size;
     */
    public void remove(Object key) {}
}


