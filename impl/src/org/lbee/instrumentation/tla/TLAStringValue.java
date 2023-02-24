package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.TrackedValue;

public class TLAStringValue extends TrackedValue<String> {

    private final String value;

    public TLAStringValue(String value) {
        this.value = value;
    }

    @Override
    public String getValue() {
        return this.value;
    }

    @Override
    public String getType() {return "string"; }

}
