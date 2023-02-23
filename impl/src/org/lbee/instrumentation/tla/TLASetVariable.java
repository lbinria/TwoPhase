package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.FormalValue;

public class TLASetVariable<TFormalValue extends FormalValue<?>> extends TLAVariable {

    public void add(TFormalValue value) {
        this.apply("AddElement", value);
    }

    public void add(TFormalValue[] value) {
        // TODO implement
        this.apply("AddElement", "");
    }

}
