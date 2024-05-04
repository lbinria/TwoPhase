package org.lbee;

import org.lbee.instrumentation.trace.TLATracer;
import org.lbee.instrumentation.clock.ClockException;
import org.lbee.instrumentation.clock.ClockFactory;
import org.lbee.network.NetworkManager;
import org.lbee.protocol.Manager;
import org.lbee.protocol.ResourceManager;
import org.lbee.protocol.TransactionManager;

import java.io.IOException;
import java.net.Socket;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.List;

/**
 * Client manager (transaction manager or resource manager)
 */
public class Client {

    public static void main(String[] args) throws IOException, ClockException {

        if (args.length < 5) {
            System.out.println("Missing arguments. hostname, port, type={tm, rm}, rmName, duration expected.");
            return;
        }
        // Get hostname, port and type of manager
        final String hostname = args[0];
        final int port = Integer.parseInt(args[1]);
        final String type = args[2];
        final String managerName = args[3];
        final int nbManagers = args.length - 5;
        final int duration = Integer.parseInt(args[args.length - 1]);

        try (Socket socket = new Socket(hostname, port)) {
            final Manager manager;
            NetworkManager networkManager = new NetworkManager(socket);
            TLATracer spec = TLATracer.getTracer(managerName + ".ndjson",
                    ClockFactory.getClock(ClockFactory.FILE,"twophase.clock"));
                    // ClockFactory.getClock(ClockFactory.SERVER, "localhost", "6666"));
            switch (type) {
                case "tm" -> {
                    List<String> rmNames = new ArrayList<>();
                    for (int i = 0; i < nbManagers; i++) {
                        rmNames.add(args[i + 4]);
                    }
                    manager = new TransactionManager(networkManager, managerName, rmNames, duration, spec);
                }
                case "rm" -> {
                    String tmName = args[4];
                    manager = new ResourceManager(networkManager, managerName, tmName, duration, spec);
                }
                default -> {
                    System.out.println("Expected type is tm or rm.");
                    return;
                }
            }
            manager.run();
            // Send bye to server (kill the server thread)
            networkManager.sendRaw("bye");
        } catch (UnknownHostException ex) {
            System.out.println("Server not found: " + ex.getMessage());
        } catch (IOException ex) {
            System.out.println("I/O error: " + ex.getMessage());
        }
    }

}