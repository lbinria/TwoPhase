package org.lbee.twophase;

public class TLAStringValue implements FormalValue {

    private final String value;

    public TLAStringValue(String value) {
        this.value = value;
    }

    @Override
    public String toString() {
        return this.value;
    }
}
