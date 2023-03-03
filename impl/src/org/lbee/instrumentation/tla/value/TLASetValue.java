package org.lbee.instrumentation.tla.value;

import org.lbee.instrumentation.TrackedValue;

public class TLASetValue<T extends TrackedValue> extends TLACollectionValue<T> {
    @Override
    public String getType() {
        return "set";
    }
}
