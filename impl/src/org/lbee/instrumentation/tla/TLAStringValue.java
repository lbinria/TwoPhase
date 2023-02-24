package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackedValue;

public class TLAStringValue extends TrackedValue<String> {

    public TLAStringValue(String value) {
        super(value, "string");
    }

    @Override
    public String toString() {
        return "{\"type\":\"" + this.getType() + "\",\"value\":\"" + this.getValue() + "\"}";
    }
}
