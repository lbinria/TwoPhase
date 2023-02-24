package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackableValue;
import org.lbee.instrumentation.TrackedVariable;

public class TLASetVariable<TValue extends TrackableValue<?>> extends TrackedVariable {

    public void add(TValue value) {
        this.apply("AddElement", value);
    }

    public void add(TValue[] value) {
        // TODO implement
        this.apply("AddElement", new TLAStringValue(""));
    }

    @Override
    public void set(TrackableValue value) {
        this.apply("Replace", value);
    }

}
