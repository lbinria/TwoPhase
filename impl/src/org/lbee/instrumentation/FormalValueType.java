package org.lbee.instrumentation;

import java.lang.annotation.ElementType;
import java.lang.annotation.Target;

@Target(ElementType.TYPE)
public @interface FormalValueType {

    String type();

}
