package org.lbee.instrumentation.tla.value;

public class TLABoolValue extends TLAPrimitiveValue<Boolean> {

    public TLABoolValue(boolean value) {
        super(value);
    }

    @Override
    public String getType() {
        return "bool";
    }

}
