package com.nsg.nsgdtlibrary.Classes.util;

import android.content.Context;
import android.graphics.Bitmap;
import android.graphics.Canvas;
import android.graphics.drawable.Drawable;
import android.location.Location;
import android.preference.PreferenceManager;
import android.util.Log;

import androidx.core.content.ContextCompat;

import com.google.android.gms.maps.model.BitmapDescriptor;
import com.google.android.gms.maps.model.BitmapDescriptorFactory;
import com.google.android.gms.maps.model.LatLng;
import com.google.maps.android.PolyUtil;
import com.google.maps.android.SphericalUtil;
import com.nsg.nsgdtlibrary.Classes.database.dto.RouteT;

import org.json.JSONException;
import org.json.JSONObject;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.IOException;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.math.BigDecimal;
import java.net.HttpURLConnection;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;

import static java.lang.Math.atan2;
import static java.lang.Math.cos;
import static java.lang.Math.sin;

class Utils {

    static final String KEY_REQUESTING_LOCATION_UPDATES = "requesting_locaction_updates";

    /**
     * Returns true if requesting location updates, otherwise returns false.
     *
     * @param context The {@link Context}.
     */
    static boolean requestingLocationUpdates(Context context) {
        return PreferenceManager.getDefaultSharedPreferences(context)
                .getBoolean(KEY_REQUESTING_LOCATION_UPDATES, false);
    }

    /**
     * Stores the location updates state in SharedPreferences.
     * @param requestingLocationUpdates The location updates state.
     */
    static void setRequestingLocationUpdates(Context context, boolean requestingLocationUpdates) {
        PreferenceManager.getDefaultSharedPreferences(context)
                .edit()
                .putBoolean(KEY_REQUESTING_LOCATION_UPDATES, requestingLocationUpdates)
                .apply();
    }

    /**
     * Returns the {@code location} object as a human readable string.
     * @param location  The {@link Location}.
     */
    static String getLocationText(Location location) {
        return location == null ? "Unknown location" :
                "(" + location.getLatitude() + ", " + location.getLongitude() + ")";
    }

    static double getAngle(LatLng beginLatLng, LatLng endLatLng) {

        if(beginLatLng == null || endLatLng == null) {
            return 0d;
        }
        double f1 = Math.PI * beginLatLng.latitude / 180;
        double f2 = Math.PI * endLatLng.latitude / 180;
        double dl = Math.PI * (endLatLng.longitude - beginLatLng.longitude) / 180;
        return atan2(sin(dl) * cos(f2), cos(f1) * sin(f2) - sin(f1) * cos(f2) * cos(dl));
    }

    static double bearingBetweenLocations(LatLng latLng1, LatLng latLng2) {
        double PI = 3.14159;
        double lat1 = latLng1.latitude * PI / 180;
        double long1 = latLng1.longitude * PI / 180;
        double lat2 = latLng2.latitude * PI / 180;
        double long2 = latLng2.longitude * PI / 180;
        double dLon = (long2 - long1);
        double y = sin(dLon) * cos(lat2);
        double x = cos(lat1) * sin(lat2) - sin(lat1)
                * cos(lat2) * cos(dLon);
        double brng = atan2(y, x);
        brng = Math.toDegrees(brng);
        brng = (brng + 360) % 360;
        return brng;
    }

    static double showDistance(LatLng latLng1, LatLng latLng2) {
        double distance = SphericalUtil.computeDistanceBetween(latLng1, latLng2);
        return distance;
    }

    static void InsertAllRouteData(String stNode, String destNode, String routeData) {

        StringBuilder query = new StringBuilder("INSERT INTO ");
        query.append(RouteT.TABLE_NAME).append("(startNode,endNode,routeData) values (")
                .append("'").append(stNode).append("',")
                .append("'").append(destNode).append("',")
                .append("'").append(routeData).append("')");
        Log.e("query", " INSERTION query--" + query);
        //sqlHandler.executeQuery(query.toString());
        //sqlHandler.closeDataBaseConnection();
    }

    static BitmapDescriptor bitmapDescriptorFromVector(Context context, int vectorResId) {
        if(context == null) {
            return null;
        }
        Drawable vectorDrawable = ContextCompat.getDrawable(context, vectorResId);
        vectorDrawable.setBounds(10, 0, vectorDrawable.getIntrinsicWidth(), vectorDrawable.getIntrinsicHeight());
        Bitmap bitmap = Bitmap.createBitmap(vectorDrawable.getIntrinsicWidth(), vectorDrawable.getIntrinsicHeight(), Bitmap.Config.ARGB_8888);
        Canvas canvas = new Canvas(bitmap);
        vectorDrawable.draw(canvas);
        return BitmapDescriptorFactory.fromBitmap(bitmap);
    }

    static LatLng findNearestPoint(final LatLng p, final LatLng start, final LatLng end) {
        if (start.equals(end)) {
            return start;
        }
        final double s0lat = Math.toRadians(p.latitude);
        final double s0lng = Math.toRadians(p.longitude);
        final double s1lat = Math.toRadians(start.latitude);
        final double s1lng = Math.toRadians(start.longitude);
        final double s2lat = Math.toRadians(end.latitude);
        final double s2lng = Math.toRadians(end.longitude);

        double s2s1lat = s2lat - s1lat;
        double s2s1lng = s2lng - s1lng;
        final double u = ((s0lat - s1lat) * s2s1lat + (s0lng - s1lng) * s2s1lng)
                / (s2s1lat * s2s1lat + s2s1lng * s2s1lng);
        if (u <= 0) {
            return start;
        }
        if (u >= 1) {
            return end;
        }

        return new LatLng(start.latitude + (u * (end.latitude - start.latitude)),
                start.longitude + (u * (end.longitude - start.longitude)));
    }

    static int setEstimatedTime(List<LatLng> points) {
        return (int) (SphericalUtil.computeLength(points) * (3600f / (NSGIMapFragmentActivity.AVERAGE_SPEED * 1000))); //30 km/hr
    }

    static double distFrom(double lat1, double lng1, double lat2, double lng2) {
        double earthRadius = 6371000; //meters
        double dLat = Math.toRadians(lat2 - lat1);
        double dLng = Math.toRadians(lng2 - lng1);
        double a = sin(dLat / 2) * sin(dLat / 2) +
                cos(Math.toRadians(lat1)) * cos(Math.toRadians(lat2)) *
                        sin(dLng / 2) * sin(dLng / 2);
        double c = 2 * atan2(Math.sqrt(a), Math.sqrt(1 - a));
        double dist = (float) (earthRadius * c);
        return dist;
    }

    static List<LatLng> removeDuplicates(List<LatLng> pointList) {

        List<LatLng> newList = new ArrayList<>();

        if (pointList.size() == 0) {
            return newList;
        }
        newList.add(pointList.get(0));

        for (int i = 1; i < pointList.size(); i++) {
            if (!isSameCoordinate(pointList.get(i), pointList.get(i - 1))) {
                newList.add(pointList.get(i));
            }
        }

        return newList;
    }

    /**
     * @param oldRoute       previous route data
     * @param newRoute       route data got from the server
     * @param deviationPoint point in which the route API request is send and successfully received
     * @return new list of LatLng merging both list of coordinates, considering the deviationPoint
     */
    static List<LatLng> mergeRoutes(List<LatLng> oldRoute, List<LatLng> newRoute, LatLng deviationPoint) {
        List<LatLng> mergedRoute = new ArrayList<>();

        if (oldRoute == null || oldRoute.size() == 0) {
            return cloneCoordinates(newRoute);
        }

        if (newRoute == null
                || deviationPoint == null
                || newRoute.size() == 0) {
            return mergedRoute;
        }

        // find perpendicular point on old route from deviationPoint
        LatLng perpendicularPoint = findNearestPointOnLine(oldRoute, deviationPoint);

        // add the first point of old route
        mergedRoute.add(oldRoute.get(0));

        //truncate the old route till perpendicular point
        for (int i = 1; i < oldRoute.size(); i++) {
            LatLng previousPoint = oldRoute.get(i - 1);
            LatLng currentPoint = oldRoute.get(i);


//            double distanceA = SphericalUtil.computeDistanceBetween(previousPoint, perpendicularPoint);
//            double distanceB = SphericalUtil.computeDistanceBetween(previousPoint, currentPoint);
//
//            if (distanceB > distanceA) {
//                // we found the position
//                mergedRoute.add(perpendicularPoint);
//                break;
//            }

            if (PolyUtil.isLocationOnPath(perpendicularPoint, Arrays.asList(previousPoint, currentPoint), false)) {
                // we found the position
                mergedRoute.add(perpendicularPoint);
                break;
            }

            // no need else as we breaking the loop
            mergedRoute.add(currentPoint);
        }

        // add deviation point
        mergedRoute.add(deviationPoint);
        // add the new route coordinates
        mergedRoute.addAll(cloneCoordinates(newRoute));

//        Log.e("MERGE_ROUTE", "oldRoute " + reverseCoordinates(oldRoute).toString());
//        Log.e("MERGE_ROUTE", "newRoute " + reverseCoordinates(newRoute).toString());
//        Log.e("MERGE_ROUTE", "deviationPoint " + reverseCoordinate(deviationPoint).toString());
//        Log.e("MERGE_ROUTE", "perpendicularPoint " + reverseCoordinate(perpendicularPoint).toString());
//        Log.e("MERGE_ROUTE", "mergedRoute " + reverseCoordinates(mergedRoute).toString());

        return mergedRoute;
    }

    static int getRandomNumberInRange(int min, int max) {

        if (min >= max) {
            throw new IllegalArgumentException("max must be greater than min");
        }

        Random r = new Random();
        return r.nextInt((max - min) + 1) + min;
    }

    static BigDecimal truncateDecimal(double x, int numberOfDecimals) {
        if (x > 0) {
            return new BigDecimal(String.valueOf(x)).setScale(numberOfDecimals, BigDecimal.ROUND_FLOOR);
        } else {
            return new BigDecimal(String.valueOf(x)).setScale(numberOfDecimals, BigDecimal.ROUND_CEILING);
        }
    }

    static JSONObject buidJsonObject(String latLng1, String latLng2, String authorisationKey) throws JSONException {
        JSONObject buidJsonObject = new JSONObject();
        buidJsonObject.accumulate("UserData", buidJsonObject1(authorisationKey));
        buidJsonObject.accumulate("StartNode", latLng1);
        buidJsonObject.accumulate("EndNode", latLng2);
        return buidJsonObject;
    }

    static JSONObject buidJsonObject1(String authorisationKey) throws JSONException {
        JSONObject buidJsonObject1 = new JSONObject();
        buidJsonObject1.accumulate("username", "admin");
        buidJsonObject1.accumulate("password", "admin");
        buidJsonObject1.accumulate("License", authorisationKey);

        return buidJsonObject1;
    }

    static void setPostRequestContent(HttpURLConnection conn,
                                      JSONObject jsonObject) throws IOException {
        OutputStream os = conn.getOutputStream();
        BufferedWriter writer = new BufferedWriter(new OutputStreamWriter(os, "UTF-8"));
        writer.write(jsonObject.toString());
        // Log.i(LoginActivity.class.toString(), jsonObject.toString());
        writer.flush();
        writer.close();
        os.close();
    }


    static void removeDuplicatesRouteDeviated(List<LatLng> listOfPoint) {
        List<LatLng> newData = removeDuplicates(listOfPoint);
        if (newData.size() < listOfPoint.size()) {
            listOfPoint.clear();
            listOfPoint.addAll(newData);
        }
    }

    static String HttpPost(String myUrl, String latLng1, String latLng2, String authorisationKey) throws IOException, JSONException {
        StringBuilder sb = new StringBuilder();
        String LoginResponse = "";
        String result = "";
        URL url = new URL(myUrl);
        Log.v("URL ", " URL: " + url);
        HttpURLConnection conn = (HttpURLConnection) url.openConnection();
        conn.setRequestMethod("POST");
        conn.setRequestProperty("Content-Type", "application/json");
        conn.setRequestProperty("Accept", "text/plain");
        JSONObject jsonObject = buidJsonObject(latLng1, latLng2, authorisationKey);
        Log.e("JSON OBJECT", "JSON OBJECT ------- " + jsonObject);
        setPostRequestContent(conn, jsonObject);
        conn.connect();
        result = conn.getResponseMessage();
        if (conn.getResponseCode() != 200) {

        } else {
            BufferedReader br = new BufferedReader(new InputStreamReader((conn.getInputStream())));
            String output = null;
            //   System.out.println("Output from Server .... \n");
            while ((output = br.readLine()) != null) {
                System.out.println(output);
                LoginResponse = sb.append(output).append(" ").toString();

            }
        }
        conn.disconnect();
        return LoginResponse;
    }

    static List<LatLng> createPointBuffer(LatLng origin, float bufferDistance) {

        List<LatLng> points = new ArrayList<>();
        for (int i = 0; i <= 360; i += 45) {
            points.add(SphericalUtil.computeOffsetOrigin(origin, bufferDistance, i));
        }
        points.add(points.get(points.size() - 1));
        return points;
    }

    static boolean pointWithinPolygon(LatLng destinationPt, List<LatLng> destinationPtsList) {
        if (destinationPtsList != null && destinationPtsList.size() > 0) {
            return PolyUtil.containsLocation(destinationPt, destinationPtsList, false);
        }

        return false;
    }

    static LatLng findNearestPointOnLine(List<LatLng> polyline, LatLng position) {

        LatLng nearestPoint = null;
        List<LatLng> nearestEdge = new ArrayList<>();

        if (polyline.size() > 0 && polyline.size() < 2) {
            //TODO need to check
            return polyline.get(0);
        }

        if (polyline.size() == 2) {
            nearestPoint = findNearestPoint(position, polyline.get(0), polyline.get(1));
        } else {
            // polyline size is more than 2
            double smallestDistance = 0;
            for (int i = 1; i < polyline.size(); i++) {
                LatLng localNearestPoint = findNearestPoint(position, polyline.get(i - 1), polyline.get(i));
                double distance = SphericalUtil.computeDistanceBetween(localNearestPoint, position);
                if (i == 1) {
                    // for the first iteration we assigning the value to smallestDistance directly
                    smallestDistance = distance;
                    nearestPoint = localNearestPoint;

                    nearestEdge.add(polyline.get(i - 1));
                    nearestEdge.add(polyline.get(i));
                } else if (distance < smallestDistance) {
                    smallestDistance = distance;
                    nearestPoint = localNearestPoint;

                    nearestEdge.add(polyline.get(i - 1));
                    nearestEdge.add(polyline.get(i));
                }
            }

        }

        // Log.e(" -- -- polyline: ", polyline.toString());
        // Log.e(" -- -- position: ", position.toString());
        // Log.e(" -- -- nearestPoint: ", nearestPoint.toString());

        return nearestPoint;
    }

    static List<List<LatLng>> splitLineByPoint(List<LatLng> polyline, LatLng position) {

        LatLng nearestPoint = null;
        List<List<LatLng>> data = new ArrayList<>();

        List<LatLng> listA = new ArrayList<>();
        List<LatLng> listB = new ArrayList<>();

        List<LatLng> nearestEdge = new ArrayList<>();

        if (polyline.size() < 2) {
            data.add(cloneCoordinates(polyline));
            return data;
        }

        if (polyline.size() == 2) {
            nearestPoint = findNearestPoint(position, polyline.get(0), polyline.get(1));

            if (isSameCoordinate(nearestPoint, polyline.get(0)) || isSameCoordinate(nearestPoint, polyline.get(1))) {
                data.add(cloneCoordinates(polyline));
            } else {
                data.add(Arrays.asList(cloneCoordinate(polyline.get(0)), nearestPoint));
                data.add(Arrays.asList(nearestPoint, cloneCoordinate(polyline.get(1))));
            }

        } else {
            // polyline size is more than 2
            double smallestDistance = 0;
            int closestPointIndex = 0;
            for (int i = 1; i < polyline.size(); i++) {
                LatLng localNearestPoint = findNearestPoint(position, polyline.get(i - 1), polyline.get(i));
                double distance = SphericalUtil.computeDistanceBetween(localNearestPoint, position);
                if (i == 1) {
                    // for the first iteration we assigning the value to smallestDistance directly
                    smallestDistance = distance;
                    nearestPoint = localNearestPoint;

                    nearestEdge.add(polyline.get(i - 1));
                    nearestEdge.add(polyline.get(i));
                    closestPointIndex = i;

                } else if (distance < smallestDistance) {
                    smallestDistance = distance;
                    nearestPoint = localNearestPoint;

                    nearestEdge.clear();
                    nearestEdge.add(polyline.get(i - 1));
                    nearestEdge.add(polyline.get(i));
                    closestPointIndex = i;
                }
            }

            // from start point to the closest index
            listA.addAll(cloneCoordinates(polyline.subList(0, closestPointIndex)));
            listA.add(cloneCoordinate(nearestPoint));

            // from the closest index to end of list
            listB.add(cloneCoordinate(nearestPoint));
            listB.addAll(cloneCoordinates(polyline.subList(closestPointIndex, polyline.size())));

            data.add(listA);
            data.add(listB);
        }

        return data;
    }

    static LatLng reverseCoordinate(LatLng point) {
        return new LatLng(point.longitude, point.latitude);
    }

    static List<LatLng> reverseCoordinates(List<LatLng> points) {
        List<LatLng> pointReversed = new ArrayList<>();
        for (LatLng point : points) {
            pointReversed.add(reverseCoordinate(point));
        }
        return pointReversed;
        // return points.stream().map( elem -> reverseCoordinate(elem)).collect(Collectors.toList());
        //return new LatLng(point.longitude, point.latitude)
    }

    static LatLng cloneCoordinate(LatLng point) {
        if (point == null) return null;
        return new LatLng(point.latitude, point.longitude);
    }

    static List<LatLng> cloneCoordinates(List<LatLng> points) {
        List<LatLng> pointReversed = new ArrayList<>();
        for (LatLng point : points) {
            pointReversed.add(cloneCoordinate(point));
        }
        return pointReversed;
        // return points.stream().map( elem -> reverseCoordinate(elem)).collect(Collectors.toList());
        //return new LatLng(point.longitude, point.latitude)
    }

    static double calculateDistanceAlongLine(List<LatLng> polyline, LatLng from, LatLng to) {
        double distanceA = calculateDistanceAlongLineFromStart(polyline, from);
        double distanceB = calculateDistanceAlongLineFromStart(polyline, to);
        return (distanceB - distanceA);
    }

    static double calculateDistanceAlongLineFromStart(List<LatLng> polyline, LatLng position) {
        double distance = 0d;

        if (!PolyUtil.isLocationOnPath(position, polyline, false)) {
            position = findNearestPointOnLine(polyline, position);
        }


        if (isSameCoordinate(position, polyline.get(0))) {
            return 0.0d;
        } else if (isSameCoordinate(position, polyline.get(polyline.size() - 1))) {
            return SphericalUtil.computeLength(polyline);
        }

        for (int i = 0; i < polyline.size() - 1; i++) {
            LatLng pointA = polyline.get(i);
            LatLng pointB = polyline.get(i + 1);

            if (PolyUtil.isLocationOnPath(position, Arrays.asList(pointA, pointB), false)) {
                distance += SphericalUtil.computeDistanceBetween(pointA, position);
                break;
            } else {
                distance += SphericalUtil.computeDistanceBetween(pointA, pointB);
            }
        }

        return distance;
    }

    static boolean isSameCoordinate(LatLng pointA, LatLng pointB) {

        if (pointA == null || pointB == null) {
            return false;
        }

        String latPointA = truncateDecimal(pointA.latitude, 8).toString();
        String lngPointA = truncateDecimal(pointA.longitude, 8).toString();

        String latPointB = truncateDecimal(pointB.latitude, 8).toString();
        String lngPointB = truncateDecimal(pointB.longitude, 8).toString();

        return latPointA.equals(latPointB) && lngPointA.equals(lngPointB);
    }

    static float computeRotation(float fraction, float start, float end) {
        float normalizeEnd = end - start; // rotate start to 0
        float normalizedEndAbs = (normalizeEnd + 360) % 360;

        float direction = (normalizedEndAbs > 180) ? -1 : 1; // -1 = anticlockwise, 1 = clockwise
        float rotation;
        if (direction > 0) {
            rotation = normalizedEndAbs;
        } else {
            rotation = normalizedEndAbs - 360;
        }

        float result = fraction * rotation + start;
        return (result + 360) % 360;
    }

}