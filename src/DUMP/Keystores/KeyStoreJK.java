package DUMP.Keystores;

public class KeyStoreJK {
    static class Entry {
        final Object key;
        Object value;

        /*@
            ensures
                this.key == key && this.value == value;
         */
        public Entry(Object key, Object value) {
            this.key = key;
            this.value = value;
        }
    }

    private Entry[] entries;

    /*@
        ensures
            entries != null && entries.length == 0;
     */
    public KeyStoreJK() {
        this.entries = new Entry[0];
    }

    // key uniqueness done as invariant
    /*@
        invariant
            (entries.length == 0)
            || (\forall int i, j;
                0 <= i < entries.length && 0 <= j < entries.length;
                i != j ==> entries[i].key != entries[j].key);
     */

    // TODO can make a method that returns a Set of keys

//    /*@ nullable */ Object /*@ strictly_pure */ get(Object key) {
//        Object result;
//        if (contains(key)) {
//            result = getValue(key);
//        }
//        else {
//            result = null;
//        }
//        return result;
//    }

    /* @
        requires contains(key);
        ensures (\forall int i; 0 <= i < entries.length; entries[i].key == key ==> getValue(key) == e.value);
     */
    private Object /*@ strictly_pure */ getValue(Object key) {
        for (int i = 0; i < entries.length; i++) {
            if (entries[i].key.equals(key)) {
                return entries[i].value;
            }
        }
        return null;
    }
}
