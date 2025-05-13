class SLL {
    //@ instance model \seq m_list;

    int key, value;
    SLL tail;
    //@ ghost \bigint length;
    //@ invariant length > 0;
    //@ invariant tail == null || tail.length + 1 == length;

    //@ represents m_list = \seq_concat(\seq_singleton(this), tail == null ? \seq_empty : tail.m_list);

    /*@ ensures this.key == key && this.value == value && this.tail == null && length == 1;
      @*/
    SLL(int key, int value) {
        this.key = key;
        this.value = value;
        this.tail = null;
        //@ set length = 1;
    }

    /*@ requires tail != null ==> tail.length >= 1;
      @ ensures this.key == key && this.value == value && this.tail == tail;
      @ ensures tail == null ==> length == 1;
      @ ensures tail != null ==> length == tail.length + 1;
      @*/
    SLL(int key, int value, SLL tail) {
        this.key = key;
        this.value = value;
        this.tail = tail;
        //@ set length = tail == null ? 1 : tail.length + 1;
    }

    /*@ normal_behavior
      @ requires elem != null && elem.tail == null;
      @ ensures \result.m_list == \seq_concat(\seq_singleton(elem), this.m_list);
      @ ensures \result.length == this.length + 1;
      @ ensures \result.key == elem.key && \result.value == elem.value && \result.tail == this;
      @ assignable \nothing;
      @*/
    SLL /*@ pure @*/ addFirst(SLL elem) {
        return new SLL(elem.key, elem.value, this);
    }

    /*@ normal_behavior
      @ requires contains(key);
      @ ensures !contains(key);
      @ ensures length == \old(length) - 1;
      @ ensures (\exists \bigint i; 0 <= i && i < \old(length); 
      @         \old(m_list)[i] == \seq_singleton(this) && m_list == \seq_concat(\old(m_list)[0..i], \old(m_list)[i+1..\old(length)]));
      @ assignable key, value, tail, length;
      @*/
    void remove(int key) {
        if (this.key == key) {
            if (tail != null) {
                this.key = tail.key;
                this.value = tail.value;
                this.tail = tail.tail;
                //@ set length = length - 1;
            }
        } else {
            SLL ptr = this;
            while (ptr.tail != null) {
                if (ptr.tail.key == key) {
                    ptr.tail = ptr.tail.tail;
                    //@ set ptr.length = ptr.length - 1;
                    break;
                }
                ptr = ptr.tail;
            }
        }
    }

    /*@ normal_behavior
      @ ensures \result == (\exists \bigint i; 0 <= i && i < length; ((SLL)m_list[i]).key == key);
      @*/
    boolean /*@ strictly_pure @*/ containsIterative(int key) {
        boolean found = false;
        SLL ptr = this;

        /*@ 
          @
          @*/
        while (ptr != null) {
            if (ptr.key == key) {
                found = true;
            }
            ptr = ptr.tail;
        }
        return found;
    }

    /*@ normal_behavior
      @ ensures \result == (\exists \bigint i; 0 <= i && i < length; ((SLL)m_list[i]).key == key);
      @ measured_by length;
      @*/
    boolean /*@ strictly_pure @*/ contains(int key) {
        return this.key == key || (tail != null && tail.contains(key));
    }
//        SLL current = this;
//
//        /*@ loop_invariant current != null ==>
//          @   (\forall \bigint j; 0 <= j && j < (\bigint)(this.length - (current == this ? 0 : current.length + 1));
//          @     ((SLL)m_list[j]).key != key);
//          @ loop_invariant current == null ==>
//          @   (\forall \bigint j; 0 <= j && j < this.length; ((SLL)m_list[j]).key != key);
//          @ decreases current == null ? 0 : current.length;
//          @*/
//        while (current != null) {
//            if (current.key == key) {
//                return true;
//            }
//            current = current.tail;
//        }
//        return false;
//    }

    /*@ normal_behavior
      @ requires contains(key);
      @ ensures (\exists \bigint i; 0 <= i && i < length; ((SLL)m_list[i]).key == key && \result == ((SLL)m_list[i]).value);
      @ assignable \nothing;
      @ exceptional_behavior
      @ requires !contains(key);
      @ signals (IllegalArgumentException) true;
      @*/
    int /*@ strictly_pure @*/ get(int key) {
        SLL current = this;
        
        /*@ loop_invariant current != null ==>
          @   (\forall \bigint j; 0 <= j && j < (\bigint)(this.length - (current == this ? 0 : current.length + 1));
          @     ((SLL)m_list[j]).key != key);
          @ loop_invariant current == null ==>
          @   (\forall \bigint j; 0 <= j && j < this.length; ((SLL)m_list[j]).key != key);
          @ decreases current == null ? 0 : current.length;
          @*/
        while (current != null) {
            if (current.key == key) {
                return current.value;
            }
            current = current.tail;
        }
        throw new IllegalArgumentException("Key not found");
    }
}