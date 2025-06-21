package DUMP.Keystores;

public class KeyStore {
    SLL[] buckets;
//    public DUMP.Keystors.KeyStore() {
//        entries = new Entry[10];
//    }

    void put(int key, int value) {
        int indexToPutAt = hash(key);

        if (buckets[indexToPutAt] == null) {
            // first value to be put in bucket
            buckets[indexToPutAt] = new SLL(key, value);
        }
//
//        else {
//            Entry entry = findIfExists(entries[indexToPutAt], key);
//            if (entry == null) {
//                // insert at front of the list
//                entry = new Entry(entries[indexToPutAt], key, value);
//                entries[indexToPutAt] = entry;
//            }
//            else {
//                // replace value of existing entry containing the key
//                entry.value = value;
//            }
//        }
    }

    int get(int key) {
        return 0;
    }

    boolean remove(int key) {
        return false;
    }

    int hash(int key) {
        return key % buckets.length;
    }
}

//class SLL2 {
//    //@ instance model \seq m_list;
//
//    int key, value;
//    SLL2 tail;
//    //@ ghost \bigint length
//    //@ invariant length > 0
//    //@ invariant tail == null || tail.length + 1 == length
//
//    //@ represents m_list = \seq_concat(\seq_singleton(this), tail == null ? \seq_empty : tail.m_list)
//
//    /*@ ensures this.key == key && this.value == value
//      @*/
//    SLL2(int key, int value) {
//        this.key = key;
//        this.value = value;
//        tail = null;
//    }
//
//    /*@ ensures this.key == key && this.value == value && this.tail == tail
//      @*/
//    SLL2(int key, int value, SLL2 tail) {
//        this.key = key;
//        this.value = value;
//        this.tail = tail;
//    }
//
//    /*@ normal_behaviour
//      @ requires elem != null
//      @ ensures \result.m_list = \seq_concat(\seq_singleton(elem), m_list)
//      @*/
//    SLL2 /*@ pure @*/ concat(int key, int value) {
//        return new SLL2(key, value, this);
//    }
//
//    /*@ requires contains(key)
//      @ ensures !contains(key)
//      @ ensures length == \old(length) - 1
//      @ ensures (\exists \bigint i; 0 <= i && i <= \old(length);
//      @*/
//    void remove(int key) {
//        if (head.key == key) {
//            this.head = tail.head;
//            this.tail = tail.tail;
//        }
//        else {
//            SLL2 ptr = this;
//
//            while (ptr.tail != null) {
//                if (ptr.tail.head.key == key) {
//
//                    break;
//                }
//                else {
//                    ptr = ptr.tail;
//                }
//            }
//        }
//    }
//
//    boolean /*strictly_pure*/ contains(int key) {
//
//    }
//
//    int /*strictly_pure*/ get(int key) {
//
//    }
//}
