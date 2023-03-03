package org.lbee.instrumentation.tla.value;

public class TLAStringValue extends TLAPrimitiveValue<String> {

    public TLAStringValue(String value) {
        super(value);
    }

    @Override
    public String getType() {
        return "string";
    }
}
