package org.lbee.instrumentation.tla;

import org.lbee.instrumentation.FormalValue;
import org.lbee.instrumentation.FormalValueType;

@FormalValueType(type="string")
public class TLAStringValue implements FormalValue<String> {

    private final String value;

    public TLAStringValue(String value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return this.value;
    }

    @Override
    public String getValue() {
        return this.value;
    }

}
