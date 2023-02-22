package org.lbee.twophase;

public class TLASetValue<T> extends TLAValue {

    public void add(T value) {
        this.apply("AddElement", value.toString());
    }

    public void add(T[] value) {
        // TODO implement
        this.apply("AddElement", "");
    }

}
