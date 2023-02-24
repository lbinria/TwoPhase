package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackedValue;

public class TLASetValue extends TrackedValue<TrackedValue<?>[]> {

    public TLASetValue(TrackedValue<?>... values) {
        super(values, "set");
    }

}
