package org.lbee.instrumentation.tla.value;

public class TLAIntValue extends TLAPrimitiveValue<Integer> {

    public TLAIntValue(Integer value) {
        super(value);
    }

    @Override
    public String getType() {
        return "int";
    }
}
