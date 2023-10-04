package org.lbee;

import com.google.gson.JsonObject;

import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.helper.ConfigurationManager;
import org.lbee.instrumentation.clock.SharedClock;
import org.lbee.network.NetworkManager;
import org.lbee.protocol.Configuration;
import org.lbee.protocol.Manager;
import org.lbee.protocol.ResourceManager;
import org.lbee.protocol.TransactionManager;

import java.io.IOException;
import java.net.Socket;
import java.net.UnknownHostException;

/**
 * Client manager (transaction manager or resource manager)
 */
public class Client {

    public static void main(String[] args) throws IOException {

        if (args.length < 5) {
            System.out.println("Missing arguments. hostname, port, type={tm, rm}, rmName, duration expected.");
            return;
        }
        // Get hostname, port and type of manager
        final String hostname = args[0];
        final int port = Integer.parseInt(args[1]);
        final String type = args[2];
        final String resourceManagerName = args[3];
        final int duration = Integer.parseInt(args[4]);

        final JsonObject jsonConfig = ConfigurationManager.read("twophase.ndjson.conf");
        System.out.println(jsonConfig);
        final Configuration config = new Configuration(jsonConfig);

        try (Socket socket = new Socket(hostname, port)) {
            final Manager manager;
            NetworkManager networkManager = new NetworkManager(socket);
            switch (type) {
                case "tm" -> {
                    String tmName = "tm";
                    TLATracer spec = TLATracer.getTracer(tmName + ".ndjson",
                            new SharedClock("twophase.clock"));
                    manager = new TransactionManager(networkManager, tmName, config.getResourceManagerNames(), spec);
                }
                case "rm" -> {
                    TLATracer spec = TLATracer.getTracer(resourceManagerName + ".ndjson",
                            new SharedClock("twophase.clock"));
                    manager = new ResourceManager(networkManager, resourceManagerName, "tm", duration, spec);
                }
                default -> {
                    System.out.println("Expected type is tm or rm.");
                    return;
                }
            }
            manager.run();
            System.out.println("DONE: "+manager.getName());
            // Send bye to server (kill the server thread)
            manager.networkManager.sendRaw("bye");
        } catch (UnknownHostException ex) {
            System.out.println("Server not found: " + ex.getMessage());
        } catch (IOException ex) {
            System.out.println("I/O error: " + ex.getMessage());
        }
    }

}
