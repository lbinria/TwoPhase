package org.lbee.instrumentation.config;

import java.util.List;

public record Operator(String method, String targetOperator,
                       List<OperatorArgumentType> args) {

}
