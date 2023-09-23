package org.lbee.protocol;

import com.google.gson.JsonArray;
import com.google.gson.JsonElement;
import com.google.gson.JsonObject;

import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;

public class Configuration {

    public TransactionManagerConfiguration tmConfig;
    public ResourceManagerConfiguration rmConfig;
    private final List<String> resourceManagerNames;

    public Configuration(JsonObject jsonConfig) {
        resourceManagerNames = jsonConfig.get("RM").getAsJsonArray().asList().stream()
                .map(JsonElement::getAsString).toList();
        this.tmConfig = new TransactionManagerConfiguration(resourceManagerNames, resourceManagerNames.size(),
                Integer.MAX_VALUE);
        this.rmConfig = new ResourceManagerConfiguration(false, -1);

    }

    public List<String> getResourceManagerNames() {
        return List.copyOf(resourceManagerNames);
    }

    @Override
    public String toString() {
        return "Configuration{" +
                "transactionManagerConfig=" + tmConfig +
                ", resourceManagerConfig=" + rmConfig +
                '}';
    }

}

/**
 * Configuration of a resource manager
 * 
 * @param shouldFail   Is resource manager should fail, invoke an unknown
 *                     exception
 * @param taskDuration Duration of the simulated task
 */
record ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {

    ResourceManagerConfiguration(boolean shouldFail, int taskDuration) {
        this.shouldFail = shouldFail;

        if (taskDuration == -1)
            /* Set a random task duration */
            this.taskDuration = new Random().nextInt(500);
        else
            this.taskDuration = taskDuration;
    }

    @Override
    public String toString() {
        return "ResourceManagerConfiguration{" +
                "shouldFail=" + shouldFail +
                ", taskDuration=" + taskDuration +
                '}';
    }
}

/**
 * Configuration of a resource manager
 * 
 * @param timeout Is resource manager should fail, invoke an unknown exception
 */
record TransactionManagerConfiguration(List<String> resourceManagerNames, int nResourceManager, int timeout) {
    @Override
    public String toString() {
        return "TransactionManagerConfiguration{" +
                "timeout=" + timeout +
                '}';
    }
}