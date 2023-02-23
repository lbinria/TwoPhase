package org.lbee.twophase;

public class TLASetVariable<TFormalValue extends FormalValue> extends TLAVariable {

    public void add(TFormalValue value) {
        this.apply("AddElement", value.toString());
    }

    public void add(TFormalValue[] value) {
        // TODO implement
        this.apply("AddElement", "");
    }

}
