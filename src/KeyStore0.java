// @ classpath "/usr/lib/jvm/java-1.8.0-openjdk-amd64/jre/lib/rt.jar"

public class KeyStore0 {

    static class Entry {
        int key, value;
        public Entry(int key, int value) {
            this.key = key;
            this.value = value;
        }
    }

    /*@ nullable @*/ Entry[] store = new Entry[1];
    /*@ model \seq seq_store;
      @ represents seq_store = \dl_array2seq(store);
      @*/

    /*@ invariant (\forall int i;
                  0 <= i && i < seq_store.length;
                  seq_store[i] == null || i == hash(((Entry)seq_store[i]).key));
        invariant store != null && store.length > 0;

    */

    KeyStore0() {
        store = new Entry[10];
    }

    // if location is already used, then throw an error.
    /*@ normal_behaviour
      @ requires seq_store[hash(key)] == null || ((Entry)seq_store[hash(key)]).key == key;
      @ ensures ((Entry)seq_store[hash(key)]).value == value;
      @ ensures \result == true;
      @ also
      @
      @ normal_behaviour
      @ requires seq_store[hash(key)] != null && ((Entry)seq_store[hash(key)]).key != key;
      @ ensures \result == false;
      @*/
    boolean put(int key, int value) {
        int pos = hash(key);
        if (store[pos] == null) {
            store[pos] = new Entry(key, value);
            return true;
        }
        else if (store[pos].key == key) {
            store[pos].value = value;
            return true;
        }
        else {
//            throw new IllegalStateException("Key collision");
            return false;
        }
    }

    // if key not found, throw an error
    /*@ normal_behaviour
      @ requires contains(key);
      @ ensures (\exists int i; 0 <= i && i < seq_store.length; seq_store[i] != null && ((Entry)seq_store[i]).key == key && \result == ((Entry)seq_store[i]).value);
      @
      @ also
      @
      @ normal_behaviour
      @ requires !contains(key);
      @ ensures \result == Integer.MIN_VALUE;
      @*/
    int /*@ strictly_pure @*/ get(int key) {
        int pos = hash(key);
        if (store[pos] == null || store[pos].key != key) {
//            throw new IllegalStateException();
            return Integer.MIN_VALUE;
        }
        else {
            return store[pos].value;
        }
    }

    // if key not present, throw an error
    /*
      */
    void remove(int key) {}

    /*
    * This is an interesting case for reflection - the contains method should speak of whether an element is present or not.
    * However, because of the design of the structure, this amounts to checking a single index to which the entry hashes.
    * Ahh so this should be specified by a class invariant. Should be provable then.
    */

    /*@ ensures \result == (\exists int i; 0 <= i && i < seq_store.length; seq_store[i] != null && ((Entry)seq_store).key == key);
      @*/
    boolean /*@ strictly_pure */ contains(int key) {
        int pos = hash(key);
        return store[pos] != null && store[pos].key == key;
    }

    /*@ normal_behaviour
      @ requires store != null && store.length > 0 && store.length <= Integer.MAX_VALUE;
      @ ensures 0 <= \result && \result < store.length;
      @*/
    /*@ strictly_pure @*/ int hash(int key) {
        return key % store.length;
    }
}

class MyException extends Exception {

}

