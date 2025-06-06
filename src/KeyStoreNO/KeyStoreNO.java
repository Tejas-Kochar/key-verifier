package KeyStoreNO;

public class KeyStoreNO {
    private int[] keys = new int[10];
    private /*@nullable*/ Object[] values = new Object[10];

    private int size;

    /*@
        private invariant keys != null && values != null && keys != values;
        private invariant keys.length == values.length;
        private invariant 0 <= size && size <= keys.length;
        private invariant (\forall int i; 0 <= i && i < size; values[i] != null);
        // unique keys
        private invariant (\forall int x, y; 0 <= x && x < y && y < size; keys[x] != keys[y]);

        private invariant \typeof(keys) == \type(int[]) && \typeof(values) == \type(Object[]);
     */

    /*@ public normal_behaviour
       ensures \result == (size > 0 && (\exists int i; 0 <= i && i < size; keys[i] == key));
    */
    public boolean /*@pure*/ contains(int key) {
        /*@ loop_invariant 0 <= i && i <= size
          @  && (\forall int x; 0 <= x && x < i; keys[x] != key);
          @ assignable \nothing;
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            if(keys[i] == key) {
                return true;
            }
        }
        return false;
    }

    /*@ public normal_behaviour
        ensures contains(key) ==> 0 <= \result < size && keys[\result] == key;
        ensures !contains(key) ==> \result == -1;
//       ensures \result == -1 ? !contains(key) : keys[\result] == key;
    */
    public int /*@pure*/ findIndex(int key) {
        /*@ loop_invariant 0 <= i && i <= size
          @  && (\forall int x; 0 <= x && x < i; keys[x] != key);
          @ assignable \nothing;
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            if(keys[i] == key) {
                return i;
            }
        }
        return -1;
    }


    /*@
        public normal_behaviour
        ensures contains(key) ==> \result == values[findIndex(key)];
        ensures !contains(key) ==> \result == null;
        assignable \strictly_nothing;
//        requires contains(key);
//        ensures (\exists int i; 0 <= i < size;
//                keys[i] == key && \result == values[i]);
//        ensures \old(size) == size;
//        assignable \strictly_nothing;
//
//        also
//
//        public normal_behaviour
//        requires !contains(key);
//        ensures \result == null;
//        ensures \old(size) == size;
//        assignable \strictly_nothing;
    */
    public /*@nullable*/ Object /*@pure*/ get(int key) {
        int index = findIndex(key);
        if(index == -1) {
            return null;
        }
        else {
            return values[index];
        }

//        /*@
//            loop_invariant 0 <= i <= size
//                && (\forall int x; 0 <= x && x < i; keys[x] != key);
//            assignable \strictly_nothing;
//            decreases size - i;
//        */
//        for (int i = 0; i < size; i++) {
//            if(keys[i] == key) {
//                return values[i];
//            }
//        }
//        return null;
    }

    /*@ public normal_behavior
      @   assignable keys, values;
      @   ensures \fresh(keys) && \fresh(values);
      @   ensures keys.length > \old(keys.length);
      @   ensures (\forall int x; 0 <= x && x < size; keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
      @*/
    public void enlarge() {
        final int[] newKeys = new int[keys.length == 0 ? 10 : keys.length*2];
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
//        requires contains(key) || size < keys.length;
//        ensures get(key) == value;
//        ensures (\forall int x; 0 <= x < \old(size) && keys[x] != key; keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
        requires !contains(key) && size < keys.length;
        ensures get(key) == value;
        ensures (\forall int x; 0 <= x < size - 1; keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
        ensures size == \old(size) + 1;
        assignable keys[*], values[*], size;

        also

        public normal_behaviour
        requires contains(key);
        ensures get(key) == value;
        ensures size == \old(size);
        ensures (\forall int x; 0 <= x < size && x != findIndex(key);
                keys[x] == \old(keys[x]) && values[x] == \old(values[x]));
//        assignable values[*];
    */
    public void putV2(int key, Object value) {
        int index = findIndex(key);
        if (index == -1) {
//            if (size == keys.length) {
//                enlarge();
//            }
            keys[size] = key;
            values[size++] = value;
        }
        else {
            values[index] = value;
        }
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
    public void put(int key, Object value) {
        if (!contains(key)) {
            if (size == keys.length) {
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

    /*@
        public normal_behaviour
        ensures !contains(key);
//        ensures size == \old(size) - (contains(key) ? 1 : 0);
        ensures (\forall int x; 0 <= x < size;
                (keys[x] == \old(keys[x]) && values[x] == \old(values[x]))
                || (keys[x] == \old(keys[size-1]) && values[x] == \old(values[size-1])));
//        ensures (\exists int x; 0 <= x < size; keys[x] == \old(keys[size-1]) && values[x] == \old(values[size-1]));
     */
    public void remove(int key) {
        int index = findIndex(key);
        if (index != -1) {
            size --;
            keys[index] = keys[size];
            values[index] = values[size];
        }
    }
}
