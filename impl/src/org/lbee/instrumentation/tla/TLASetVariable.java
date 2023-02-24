package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackableValue;
import org.lbee.instrumentation.TrackedVariable;

public class TLASetVariable<TFormalValue extends TrackableValue<?>> extends TrackedVariable {

    public void add(TFormalValue value) {
        this.apply("AddElement", value);
    }

    public void add(TFormalValue[] value) {
        // TODO implement
        this.apply("AddElement", "");
    }

    @Override
    public void set(TrackableValue value) {
        this.apply("Replace", value);
    }

    @Override
    public String getType() { return "set"; }
}
