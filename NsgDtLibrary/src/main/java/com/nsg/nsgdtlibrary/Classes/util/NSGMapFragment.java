package com.nsg.nsgdtlibrary.Classes.util;

import android.Manifest;
import android.animation.ValueAnimator;
import android.annotation.SuppressLint;
import android.app.Activity;
import android.app.AlertDialog;
import android.content.Context;
import android.content.DialogInterface;
import android.content.Intent;
import android.content.pm.PackageManager;
import android.graphics.Bitmap;
import android.graphics.BitmapFactory;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Point;
import android.graphics.drawable.Drawable;
import android.location.Location;
import android.location.LocationManager;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.os.Handler;
import android.os.Looper;
import android.speech.tts.TextToSpeech;
import android.util.Log;
import android.view.Gravity;
import android.view.LayoutInflater;
import android.view.MenuItem;
import android.view.View;
import android.view.ViewGroup;
import android.view.animation.LinearInterpolator;
import android.widget.Button;
import android.widget.EditText;
import android.widget.ImageButton;
import android.widget.ImageView;
import android.widget.PopupMenu;
import android.widget.TextView;
import android.widget.Toast;

import com.google.android.gms.location.FusedLocationProviderClient;
import com.google.android.gms.location.LocationCallback;
import com.google.android.gms.location.LocationRequest;
import com.google.android.gms.location.LocationResult;
import com.google.android.gms.location.LocationServices;
import com.google.android.gms.maps.CameraUpdateFactory;
import com.google.android.gms.maps.GoogleMap;
import com.google.android.gms.maps.OnMapReadyCallback;
import com.google.android.gms.maps.Projection;
import com.google.android.gms.maps.SupportMapFragment;
import com.google.android.gms.maps.model.BitmapDescriptor;
import com.google.android.gms.maps.model.BitmapDescriptorFactory;
import com.google.android.gms.maps.model.CameraPosition;
import com.google.android.gms.maps.model.Circle;
import com.google.android.gms.maps.model.CircleOptions;
import com.google.android.gms.maps.model.LatLng;
import com.google.android.gms.maps.model.MapStyleOptions;
import com.google.android.gms.maps.model.Marker;
import com.google.android.gms.maps.model.MarkerOptions;
import com.google.android.gms.maps.model.Polyline;
import com.google.android.gms.maps.model.PolylineOptions;
import com.google.android.gms.maps.model.TileOverlay;
import com.google.android.gms.maps.model.TileOverlayOptions;
import com.google.android.gms.maps.model.TileProvider;
import com.google.android.gms.tasks.OnSuccessListener;
import com.google.maps.android.PolyUtil;
import com.google.maps.android.SphericalUtil;
import com.nsg.nsgdtlibrary.Classes.activities.AppConstants;
import com.nsg.nsgdtlibrary.Classes.activities.ExpandedMBTilesTileProvider;
import com.nsg.nsgdtlibrary.Classes.activities.GpsUtils;
import com.nsg.nsgdtlibrary.Classes.database.dto.EdgeDataT;
import com.nsg.nsgdtlibrary.Classes.database.dto.RouteT;
import com.nsg.nsgdtlibrary.R;

import org.json.JSONArray;
import org.json.JSONException;
import org.json.JSONObject;

import java.io.File;
import java.io.IOException;
import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Locale;
import java.util.Timer;
import java.util.TimerTask;

import androidx.annotation.NonNull;
import androidx.annotation.RequiresApi;
import androidx.core.app.ActivityCompat;
import androidx.core.content.ContextCompat;
import androidx.fragment.app.Fragment;

import static android.Manifest.permission.ACCESS_FINE_LOCATION;
import static android.Manifest.permission.READ_EXTERNAL_STORAGE;
import static android.content.Context.LOCATION_SERVICE;
import static java.lang.Math.atan2;
import static java.lang.Math.cos;
import static java.lang.Math.sin;

public class NSGMapFragment extends Fragment implements View.OnClickListener  {
    private boolean isAlertShown = false;
    private static final int PERMISSION_REQUEST_CODE = 200;
    boolean locationAccepted, islocationControlEnabled = false;
    // private static final int SENSOR_DELAY_NORMAL =50;
    boolean isTimerStarted = false;
    private TextToSpeech textToSpeech;
    LatLng oldGPSPosition;
    Marker mPositionMarker;
    private GoogleMap mMap;
    private List points;
    private List<LatLng> convertedPoints;
    private Marker sourceMarker, destinationMarker;

    private int routeDeviationDistance;
    private Circle mCircle = null;
    Bitmap mMarkerIcon;

    private List<LatLng> currentRouteData = new ArrayList<LatLng>();
    private List<LatLng> currentDeviatedRouteData = new ArrayList<>();
    private List<LatLng> deviatedRouteData = new ArrayList<>();

    HashMap<String, String> AllPointEdgeNo;
    HashMap<String, String> AllPointEdgeDistaces;
    private LatLng PointData;
    private List<LatLng> nearestPointValuesList;
    private ImageButton change_map_options, re_center;
    private List<LatLng> OldNearestGpsList;
    private String BASE_MAP_URL_FORMAT;
    private LatLng SourceNode, DestinationNode;
    LatLng currentGpsPosition;
    float azimuthInDegress;
    Timer myTimer = new Timer();
    private String stNode, endNode, routeDeviatedDT_URL = "", AuthorisationKey;
    double TotalDistanceInMTS;
    private List<EdgeDataT> EdgeContainsDataList;
    StringBuilder time = new StringBuilder();
    LatLng currentPerpendicularPoint = null;
    private String routeData;
    public boolean isMapLoaded = false;
    public boolean isNavigationStarted = false;
    LocationManager mLocationManager;

    private TextView txtLocation;

    private FusedLocationProviderClient mFusedLocationClient;
    private double wayLatitude = 0.0, wayLongitude = 0.0;
    private LocationRequest locationRequest;
    private LocationCallback locationCallback;
    private StringBuilder stringBuilder;
    LatLng currentGPSPosition;
    private boolean isContinue = true;
    private String GeoFenceCordinates;
    private boolean routeAPIHit = false;
    List<LatLng> commonPoints = new ArrayList<LatLng>();
    List<LatLng> uncommonPoints = new ArrayList<LatLng>();

    //
    List<Double> consDistList = new ArrayList<>();
    List<LatLng> destinationGeoFenceCoordinatesList;
    private boolean isLieInGeofence = false;
    private boolean isContinuoslyOutOfTrack = false;
    boolean httpRequestFlag = false;
    private EditText dynamic_changeValue;
    private Button submit;

    long startTimestamp;
    int estimatedRemainingTime = 0;

    private static int CURRENT_ROUTE_COLOR = Color.CYAN;
    private static int DEVIATED_ROUTE_COLOR = Color.RED;

    private static int CURRENT_ROUTE_WIDTH = 25;
    private static int DEVIATED_ROUTE_WIDTH = 25;

    List<RouteMessage> messageContainer = new ArrayList<>();

    List<RouteMessage> messageContainerTemp = new ArrayList<>();

    PolylineOptions currentPolylineOptions = new PolylineOptions();
    Polyline currentPolylineGraphics = null;

    PolylineOptions deviatedPolylineOptions = new PolylineOptions();
    Polyline deviatedPolylineGraphics = null;

    private static double MINIMUM_VEHICLE_SPEED = 30d; // KM/HR

    private int estimatedTimeInSeconds = 0;
    private static int AVERAGE_SPEED = 30;

    private boolean isETACrossed = false;

    private List<EdgeDataT> edgeDataList;

    private LatLng nearlyFirstGPSPosition = null;

    public interface FragmentToActivity {
        String communicate(String comm, int alertType);
    }

    private FragmentToActivity Callback;

    public NSGMapFragment() {
    }

    @SuppressLint("ValidFragment")
    public NSGMapFragment(String BASE_MAP_URL_FORMAT) {
        this.BASE_MAP_URL_FORMAT = BASE_MAP_URL_FORMAT;
    }

    @SuppressLint("ValidFragment")
    public NSGMapFragment(String BASE_MAP_URL_FORMAT, String stNode, String endNode, String routeData, int routeDeviationBuffer, String routeDeviatedDT_URL, String AuthorisationKey, String GeoFenceCordinates) {
        this.BASE_MAP_URL_FORMAT = BASE_MAP_URL_FORMAT;
        this.stNode = stNode;
        this.endNode = endNode;
        this.routeDeviationDistance = routeDeviationBuffer;
        this.routeData = routeData;
        this.routeDeviatedDT_URL = routeDeviatedDT_URL;
        this.AuthorisationKey = AuthorisationKey;
        this.GeoFenceCordinates = GeoFenceCordinates;
    }
    @Override
    public void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setHasOptionsMenu(true);
        mLocationManager = (LocationManager) getActivity().getSystemService(LOCATION_SERVICE);
        if (savedInstanceState == null) {
            textToSpeech = new TextToSpeech(getContext(), new TextToSpeech.OnInitListener() {
                @Override
                public void onInit(int status) {
                    if (status == TextToSpeech.SUCCESS) {
                        int ttsLang = textToSpeech.setLanguage(Locale.US);
                        if (ttsLang == TextToSpeech.LANG_MISSING_DATA
                                || ttsLang == TextToSpeech.LANG_NOT_SUPPORTED) {
                            Log.e("TTS", "The Language is not supported!");
                        } else {
                            Log.i("TTS", "Language Supported.");
                        }
                        Log.i("TTS", "Initialization success.");
                    } else {
                        Toast.makeText(getContext(), "TTS Initialization failed!", Toast.LENGTH_SHORT).show();
                    }
                }
            });
        }

        //Initialise Fused Location Client
        mFusedLocationClient = LocationServices.getFusedLocationProviderClient(getActivity());
        //Initialise Location Listener
        locationRequest = LocationRequest.create();
        //Initialise Accuracy
        locationRequest.setPriority(LocationRequest.PRIORITY_HIGH_ACCURACY);
        //Initialise interval
        // locationRequest.setInterval(1 * 1000); // 10 seconds
        // locationRequest.setFastestInterval(5 * 1000); // 5 seconds

        new GpsUtils(getContext()).turnGPSOn(new GpsUtils.onGpsListener() {
            @Override
            public void gpsStatus(boolean isGPSEnable) {
                // turn on GPS
//                isGPS = isGPSEnable;
            }
        });
        //getLocation callback Method for get location
        locationCallback = new LocationCallback() {
            @Override
            public void onLocationResult(LocationResult locationResult) {
                // if(islocationControlEnabled==false) {
                if (locationResult == null) {
                    return;
                }
                for (Location location : locationResult.getLocations()) {
                    if (location != null) {

                        wayLatitude = location.getLatitude();
                        wayLongitude = location.getLongitude();
                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK LAT  -- 09-JAN-2021"+wayLatitude);
                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK -- LONGI 09-JAN-2021"+wayLongitude);
                        currentGPSPosition = new LatLng(wayLatitude, wayLongitude);
                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK -- 09-JAN-2021"+currentGPSPosition);


                        if (!isContinue) {
                            txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));
                            //  Log.v("APP DATA", "APP DATA DATA ........ IF " );
                        } else {
//                            stringBuilder.append(wayLatitude);
//                            stringBuilder.append("-");
//                            stringBuilder.append(wayLongitude);
//                            stringBuilder.append("\n\n");
                            currentGPSPosition = new LatLng(wayLatitude, wayLongitude);
                            Log.e("LOCATION CALLBACK","LOCATION CALLBACK -- 09-JAN-2021"+currentGPSPosition);
                        }
                    }
                }
            }
        };
        // writeLogFile();
    }

    @Override
    public void onAttach(Context context) {
        super.onAttach(context);
        try {
            //sqlHandler = new SqlHandler(getContext());// Sqlite handler
            Callback = (FragmentToActivity) context;
        } catch (ClassCastException e) {
            throw new ClassCastException(context.toString()
                    + " must implement FragmentToActivity");
        }
    }

    @RequiresApi(api = Build.VERSION_CODES.KITKAT)
    @Override
    public View onCreateView(LayoutInflater inflater, ViewGroup container,
                             Bundle savedInstanceState) {
        //Check self permissions for Location and storage
        checkPermission();
        //Request permissions for Location and storage
        requestPermission();
        //set marker icon
        mMarkerIcon = BitmapFactory.decodeResource(getResources(), R.drawable.gps_transperent_98);
        //Initialise RootView
        View rootView = inflater.inflate(R.layout.fragment_map, container, false);
        writeLogFile();

        //Initialise Buttons

        // dynamic_changeValue = (EditText) rootView.findViewById(R.id.dynamic_buffer);
        //  submit = (Button) rootView.findViewById(R.id.submit);
        //  submit.setOnClickListener(NSGIMapFragmentActivity.this);
        re_center = (ImageButton) rootView.findViewById(R.id.re_center);
        re_center.setOnClickListener(NSGMapFragment.this);
        change_map_options = (ImageButton) rootView.findViewById(R.id.change_map_options);
        change_map_options.setOnClickListener(NSGMapFragment.this);
        // Delete Contents fron ROUTE_T On initialisation of Route view
        String delQuery = "DELETE  FROM " + RouteT.TABLE_NAME;
        SupportMapFragment mapFragment = (SupportMapFragment) getChildFragmentManager().findFragmentById(R.id.frg);  //use SuppoprtMapFragment for using in fragment instead of activity  MapFragment1 = activity   SupportMapFragment = fragment
        mapFragment.getMapAsync(new OnMapReadyCallback() {
            @Override
            public void onMapReady(GoogleMap googlemap) {
                if (BASE_MAP_URL_FORMAT != null) {
                    //Initialise GoogleMap
                    NSGMapFragment.this.mMap = googlemap;
                    //mMap.setMapType(GoogleMap.MAP_TYPE_NONE);
                    //set GoogleMap Style
                    NSGMapFragment.this.mMap.setMapStyle(MapStyleOptions.loadRawResourceStyle(getContext(), R.raw.stle_map_json));
                    //set  Tileprovider to GoogleMap
                    TileProvider tileProvider = new ExpandedMBTilesTileProvider(new File(BASE_MAP_URL_FORMAT.toString()), 256, 256);
                    TileOverlay tileOverlay = mMap.addTileOverlay(new TileOverlayOptions().tileProvider(tileProvider));
                    tileOverlay.setTransparency(0.5f - tileOverlay.getTransparency());
                    tileOverlay.setVisible(true);
                    if (routeData != null) {
                        /*Get Route From Database and plot on map*/
                        GetRouteFromDBPlotOnMap(routeData);
                        StringBuilder routeAlert = new StringBuilder();
                        routeAlert.append(MapEvents.ALERTVALUE_1).append("SourcePosition : " + SourceNode).append("Destination Node " + DestinationNode);
                        //send alert AlertTupe-1 -- started
                        sendData(routeAlert.toString(), MapEvents.ALERTTYPE_1);
                    }
                    addMarkers();
                    if (GeoFenceCordinates != null && !GeoFenceCordinates.isEmpty()) {
                       // SplitDestinationData(GeoFenceCordinates);
                    }
                    if (ActivityCompat.checkSelfPermission(getContext(), ACCESS_FINE_LOCATION) != PackageManager.PERMISSION_GRANTED && ActivityCompat.checkSelfPermission(getContext(), Manifest.permission.ACCESS_COARSE_LOCATION) != PackageManager.PERMISSION_GRANTED) {
                        // TODO: Consider calling
                        //    ActivityCompat#requestPermissions
                        return;
                    }
                    //Sending Alert Map is READY
                    isMapLoaded = true;
                    if (isMapLoaded) {
                        String MapAlert = "Map is Ready";
                        sendData(MapEvents.ALERTVALUE_6, MapEvents.ALERTTYPE_6);
                    }


                }
            }
        });
        return rootView;
    }
    public void addMarkers() {
        if (SourceNode != null && DestinationNode != null) {
            sourceMarker = mMap.addMarker(new MarkerOptions()
                    .position(SourceNode)
                    .icon(bitmapDescriptorFromVector(getActivity(), R.drawable.source_marker_whitetext)));
            CameraPosition googlePlex = CameraPosition.builder()
                    .target(SourceNode)
                    .zoom(18)
                    .tilt(45)
                    .build();
            mMap.animateCamera(CameraUpdateFactory.newCameraPosition(googlePlex), 1000, null);

            destinationMarker = mMap.addMarker(new MarkerOptions()
                    .position(DestinationNode)
                    .icon(bitmapDescriptorFromVector(getActivity(), R.drawable.destination_marker_whitetext_lightgreen)));
               /*
                CameraPosition googlePlex1 = CameraPosition.builder()
                        .target(DestinationNode)
                        .zoom(18)
                        .tilt(45)
                        .build();

                mMap.animateCamera(CameraUpdateFactory.newCameraPosition(googlePlex1), 1000, null);

                */
        } else {
            mMap.addMarker(new MarkerOptions()
                    .position(new LatLng(24.984408, 55.072814))
                    .icon(bitmapDescriptorFromVector(getActivity(), R.drawable.blue_marker)));
            CameraPosition googlePlex = CameraPosition.builder()
                    .target(new LatLng(24.984408, 55.072814))
                    .zoom(15)
                    .tilt(45)
                    .build();
            mMap.animateCamera(CameraUpdateFactory.newCameraPosition(googlePlex), 1000, null);

        }
    }


    //Main method to start the navigation
    public int startNavigation() {
            /*
                Starts Navigation HERE
                Get current location from the location service if map enabled true then it will starts navigation
                from external service and strts navigation if route deviation not observed move in the loaded path
                if route deviation observed movement from route deviated path only
             */
        islocationControlEnabled = false;
        Log.v("APP DATA ", "islocationControlEnabled START BUTTON GPS POSITION ----" + oldGPSPosition);


        if (SourceNode != null && DestinationNode != null) {

            //estimate the projected travelling time
            //setEstimatedTime(currentRouteData);

            isETACrossed = false;

            //Construct Point based on main app passed Lat/Long
            nearestPointValuesList = new ArrayList<LatLng>();
            nearestPointValuesList.add(new LatLng(SourceNode.latitude, SourceNode.longitude));

            //Construct Point based on main app passed Lat/Long
            OldNearestGpsList = new ArrayList<>();
            OldNearestGpsList.add(new LatLng(SourceNode.latitude, SourceNode.longitude));


            try {

                if (mMap != null && isMapLoaded && !isNavigationStarted) {

                    //To enable Direction text for every 8000ms
//                    if (isTimerStarted = true) {

                    myTimer.scheduleAtFixedRate(new TimerTask() {
                        @Override
                        public void run() {
                            if (currentGpsPosition != null && DestinationNode != null && isNavigationStarted) {
                                if (!islocationControlEnabled && !isContinuoslyOutOfTrack) {

                                    displayNavigationMessage(currentGpsPosition);
                                    // if (time != null && !time.toString().isEmpty() && estimatedRemainingTime > 0) {
                                    // ETA Calculation

                                    if (estimatedRemainingTime > 0) {
                                        if (getActivity() != null) {
                                            new Handler(Looper.getMainLooper()).post(new Runnable() {
                                                @Override
                                                public void run() {
                                                    String etaMessage = "";
                                                    if (estimatedRemainingTime > 60) {
                                                        int minute = estimatedRemainingTime / 60;
                                                        int sec = estimatedRemainingTime % 60;
                                                        etaMessage = "ETA: " + minute + "min. " + sec + "sec";
                                                    } else {
                                                        etaMessage = "ETA: " + estimatedRemainingTime + "sec";
                                                    }
                                                    Toast toast = Toast.makeText(getActivity().getApplicationContext(), etaMessage, Toast.LENGTH_SHORT);
                                                    toast.setMargin(70, 50);
                                                    toast.setGravity(Gravity.BOTTOM, 0, 120);
                                                    if (isETACrossed) {
                                                        toast.getView().setBackgroundColor(Color.RED);
                                                    }
                                                    toast.show();
                                                }
                                            });
                                        }
                                    }

                                }

                            }
                        }

                    }, 10L, 8000L);
//                    } //end of Timer if

                    mMap.setMyLocationEnabled(true);
                    mMap.setBuildingsEnabled(true);
                    mMap.getUiSettings().setZoomControlsEnabled(true);
                    mMap.getUiSettings().setCompassEnabled(true);
                    //  mMap.getUiSettings().setMyLocationButtonEnabled(false);
                    mMap.getUiSettings().setMapToolbarEnabled(true);
                    mMap.getUiSettings().setZoomGesturesEnabled(true);
                    mMap.getUiSettings().setScrollGesturesEnabled(true);
                    mMap.getUiSettings().setTiltGesturesEnabled(true);
                    mMap.getUiSettings().setRotateGesturesEnabled(true);
                    mMap.getUiSettings().setMyLocationButtonEnabled(true);

                    //BY DEFAULT true
                    isNavigationStarted = true;

                    if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.JELLY_BEAN) {
//                        isTimerStarted = true;
                        Handler handler = new Handler();

                        //Get Location for every 1000 ms
                        int delay = 1000 * 1; //milliseconds

                        handler.postDelayed(new Runnable() {
                            public void run() {
                                double returnedDistance_ref = 0.0;

                                if (currentGpsPosition != null) {
                                    oldGPSPosition = currentGpsPosition;
                                    //  Log.v("APP DATA ", "START NAV OLD GPS POSITION ----" + OldGPSPosition);
                                    // returnedDistance_ref = verifyDeviationCalculateDistance(OldGPSPosition, currentGpsPosition);
                                    LatLng nearest_LatLng_deviation = findNearestPointOnLine(currentRouteData, currentGpsPosition);
                                    returnedDistance_ref = SphericalUtil.computeDistanceBetween(currentGpsPosition, nearest_LatLng_deviation);
                                }

                                consDistList.add(returnedDistance_ref);
                                isContinue = true;
                                stringBuilder = new StringBuilder();

                                currentGpsPosition = getLocation();
                                //Log.e("APP DATA ", "START NAVI CURRENT GPS POSITION 09-JAN-2021 ----" + currentGpsPosition);
                                //Draw circle at current GPS with buffer configured value
                                //ACTION - CHANGES TO BE DONE

                                if (currentGpsPosition != null) {
                                  //  Log.v("APP DATA ", "START NAVI CURRENT GPS POSITION ----" + currentGpsPosition);
                                    //Draw Circle first time and update position next time
                                    // drawMarkerWithCircle(currentGpsPosition, routeDeviationDistance);
                                }

                                // Navigation code starts from here

                                //OldNearestPosition means previous point on road
                                LatLng OldNearestPosition = null;

                               /* if (oldGPSPosition != null) {

                                    //Start of the tracking
                                    if (startTimestamp == 0) {
                                        // for the first time only
                                        startTimestamp = System.currentTimeMillis();
                                    }

                                    int timeTakenTillNow = (int) (System.currentTimeMillis() - startTimestamp) / 1000;

                                    // Taking sample of current GPS position, to know from where we have started the journey
                                    if (timeTakenTillNow < 5) {
                                        nearlyFirstGPSPosition = cloneCoordinate(currentGpsPosition);
                                    }

                                    //Get the distance between
                                    double distance = distFrom(oldGPSPosition.latitude, oldGPSPosition.longitude, currentGpsPosition.latitude, currentGpsPosition.longitude);
                                    //  Log.e("distance", "distance" + distance);

                                    //if the distance between previous GPS position and current GPS position is more than 40 meters
                                    //DONT DO ANYTHING - JUST SKIP THE POINT
                                    //WHY 40 METERS? - ACTION - CHECK
                                    if (distance > 40) {

                                    } else {

                                        //currentPerpendicularPoint ---- BY DEFAULT NULL
                                        OldNearestPosition = currentPerpendicularPoint;
                                        // Log.e("CurrentGpsPoint", " OLD Nearest GpsPoint " + OldNearestPosition);

                                        currentPerpendicularPoint = findNearestPointOnLine(currentRouteData, currentGpsPosition);

                                        Log.e("CurrentGpsPoint", " Nearest GpsPoint" + currentPerpendicularPoint);

                                        //Get the perpendicular distance from GPS to Road
                                        double distance_movement = distFrom(currentPerpendicularPoint.latitude, currentPerpendicularPoint.longitude, currentGpsPosition.latitude, currentGpsPosition.longitude);

                                        //If the perpendicular distance between current GPS and road is less than 40 meters
                                        //change the position of marker to point on road
                                        //ACTION - CHANGE THIS TO BUFFER DISTANCE


                                        if (distance_movement < 40) { //Follow current route

                                            Log.e("ORGINAL DATA ", " ORIGINAL DATA----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                            //If there is no marker - create marker
                                            if (mPositionMarker == null && currentGpsPosition != null) {
                                                mPositionMarker = mMap.addMarker(new MarkerOptions()
                                                        .position(SourceNode)
                                                        .title("Nearest GpsPoint")
                                                        .anchor(0.5f, 0.5f)
                                                        .flat(true)
                                                        .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));
                                            } else { //update marker position
                                                // Log.e("CurrentGpsPoint", " currentGpsPosition ------ " + currentGpsPosition);

                                                if (OldNearestPosition != null) {
                                                    if (!islocationControlEnabled) {
                                                        Log.e("CurrentGpsPoint", " curren FRM START NAVI ------ " + currentGpsPosition);
                                                        // Log.e("CurrentGpsPoint", " Old  FRM START NAVI ------ " + OldNearestPosition);
                                                        Log.e("CurrentGpsPoint", " CGPS " + currentGpsPosition);
                                                        Log.e("CurrentGpsPoint", " per.CGPS " + currentPerpendicularPoint);


                                                        //moving the marker position from old point on road to new point on road in 1000ms
                                                        animateCarMove(mPositionMarker, OldNearestPosition, currentPerpendicularPoint, 1000);
                                                        float bearing = (float) bearingBetweenLocations(OldNearestPosition, currentPerpendicularPoint);
                                                        Log.e("MainRoute", "BEARING @@@@@@@ " + bearing);
                                                        int height = 0;
                                                        if (getView() != null) {
                                                            height = getView().getMeasuredHeight();
                                                        }
                                                        Projection p = mMap.getProjection();
                                                        Point bottomRightPoint = p.toScreenLocation(p.getVisibleRegion().nearRight);
                                                        Point center = new Point(bottomRightPoint.x / 2, bottomRightPoint.y / 2);
                                                        Point offset = new Point(center.x, (center.y + (height / 4)));
                                                        LatLng centerLoc = p.fromScreenLocation(center);
                                                        Log.e("MainRoute", "centerLoc @@@@@@@ " + centerLoc);

                                                        LatLng offsetNewLoc = p.fromScreenLocation(offset);
                                                        double offsetDistance = SphericalUtil.computeDistanceBetween(centerLoc, offsetNewLoc);
                                                        Log.e("MainRoute", "offsetDistance @@@@@@@ " + offsetDistance);
                                                        LatLng shadowTgt = SphericalUtil.computeOffset(currentPerpendicularPoint, offsetDistance, bearing);
                                                        Log.e("MainRoute", "shadowTgt @@@@@@@ " + shadowTgt);

                                                        //ETA Calculation
//                                                      calculateETA(startTimestamp, currentGpsPosition, currentRouteData);
                                                        if (timeTakenTillNow >= 5) {
                                                            calculateETA(startTimestamp, currentGpsPosition, currentRouteData);
                                                        }
                                                        //*****************************************
                                                        //If vehicle reaches destination
                                                        alertDestination(currentGpsPosition);
                                                        //isReachedDestination(currentPerpendicularPoint, DestinationNode);
                                                        //*****************************************

                                                        if (offsetDistance > 5 && bearing > 0.0) {
                                                            CameraPosition currentPlace = new CameraPosition.Builder()
                                                                    .target(shadowTgt)
                                                                    .bearing(bearing).tilt(65.5f).zoom(18)
                                                                    .build();
                                                            mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace), 1000, null);
                                                        }
                                                    } else {
                                                        animateCarMoveNotUpdateMarker(mPositionMarker, OldNearestPosition, currentPerpendicularPoint, 1000);
                                                    }


                                                } else {
                                                    // may be we need add marker animation here
                                                    //TODO
                                                }
                                            }

                                        } else { //if the perpendicular distance is more than 40 (i.e. vehicle deviated the route) (** i.e. vehicle may be deviated the route)


                                            Log.e("DEVIATION DATA ", " DEVIATION DATA----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                            // will solve the move back issue, may be
                                            currentPerpendicularPoint = null;

                                            isContinuoslyOutOfTrack = false;

                                            //Add marker first time
                                            if (mPositionMarker == null) {

                                                mPositionMarker = mMap.addMarker(new MarkerOptions()
                                                        .position(currentGPSPosition)
                                                        .title("Nearest GpsPoint")
                                                        .anchor(0.5f, 0.5f)
                                                        .flat(true)
                                                        .icon(bitmapDescriptorFromVector(getContext(), R.drawable.gps_transperent_98)));


                                            } else { //update marker position

                                                //Check three consecutive deviations to hit the API to get new route
                                                double returnedDistance1 = 0.0;
                                                double returnedDistance2 = 0.0;
                                                double returnedDistance3 = 0.0;
                                                if (consDistList != null && consDistList.size() > 2) {
                                                    returnedDistance1 = consDistList.get(consDistList.size() - 1);
                                                    //Log.e("APP DATA ", " Deviation Distance 1 ----" + returnedDistance1);
                                                    returnedDistance2 = consDistList.get(consDistList.size() - 2);
                                                    //Log.e("APP DATA ", "Deviation Distance 2 ----" + returnedDistance2);
                                                    returnedDistance3 = consDistList.get(consDistList.size() - 3);
                                                    //Log.e("APP DATA ", "Deviation Distance 3 ----" + returnedDistance3);
                                                }

                                                Log.e("ROUTE DEV MKR UPDATE", " WITHIN ROUTE DEIVATION MARKER UPDATE----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                                //Get the deviated Route
                                                if (returnedDistance1 > routeDeviationDistance
                                                        && returnedDistance2 > routeDeviationDistance
                                                        && returnedDistance3 > routeDeviationDistance) {
                                                    // Log.e("APP DATA ", "Route Deviated ----" + "YES.....");
                                                    //  Log.e("APP DATA ", " Deviation Distance 1 ----" + returnedDistance1);
                                                    //  Log.e("APP DATA ", " Deviation Distance 2 ----" + returnedDistance2);
                                                    //  Log.e("APP DATA ", " Deviation Distance 3 ----" + returnedDistance3);

                                                    Log.e("BEFR RT DEV HIT", " BEFORE ROUTE DEIVATION API HIT----" + currentGpsPosition + "," + currentPerpendicularPoint + "," + distance_movement);

                                                    // Log.e("APP DATA ", " OLD GPS ----" + OldGPSPosition);
                                                    Log.e("APP DATA ", " CGPS----" + currentGpsPosition);
                                                    //  Log.e("APP DATA ", " Per.OLD GPS----" + OldNearestPosition);
                                                    Log.e("APP DATA ", " Per.CGPS GPS-----" + currentPerpendicularPoint);

                                                    // No animation inside
                                                    //Hit API to get route and plot
                                                    verifyRouteDeviation(oldGPSPosition, currentGpsPosition, DestinationNode, routeDeviationDistance);

                                                }

                                                //map animation
                                                animateCarMove(mPositionMarker, oldGPSPosition, currentGPSPosition, 1000);
                                                float bearing = (float) bearingBetweenLocations(oldGPSPosition, currentGpsPosition);
                                                Log.e("Fallow GPS ROUTE", "BEARING : " + bearing);
                                                int height = 0;
                                                if (getView() != null) {
                                                    height = getView().getMeasuredHeight();
                                                }
                                                Projection p = mMap.getProjection();
                                                Point bottomRightPoint = p.toScreenLocation(p.getVisibleRegion().nearRight);
                                                Point center = new Point(bottomRightPoint.x / 2, bottomRightPoint.y / 2);
                                                Point offset = new Point(center.x, (center.y + (height / 4)));
                                                LatLng centerLoc = p.fromScreenLocation(center);
                                                Log.e("Fallow GPS ROUTE", "centerLoc : " + centerLoc.latitude + "," + centerLoc.longitude);
                                                LatLng offsetNewLoc = p.fromScreenLocation(offset);
                                                double offsetDistance = SphericalUtil.computeDistanceBetween(centerLoc, offsetNewLoc);
                                                Log.e("Fallow GPS ROUTE", "offsetDistance : " + offsetDistance);
                                                LatLng shadowTgt = SphericalUtil.computeOffset(currentGpsPosition, offsetDistance, bearing);
                                                Log.e("Fallow GPS ROUTE", "shadowTgt : " + shadowTgt.latitude + "," + shadowTgt.longitude);
                                                if (offsetDistance > 5 && bearing > 0.0) {
                                                    CameraPosition currentPlace_main = new CameraPosition.Builder()
                                                            .target(shadowTgt)
                                                            .bearing(bearing).tilt(65.5f).zoom(18)
                                                            .build();
                                                    mMap.animateCamera(CameraUpdateFactory.newCameraPosition(currentPlace_main), 1000, null);
                                                }
                                            }
                                        }
                                    }

                                }*/

                                //if the navigation is active then only make a recursive call
                                if(isNavigationStarted) {
                                    handler.postDelayed(this, delay);
                                } else {
                                    if( myTimer != null) {
                                        myTimer.cancel();
                                        myTimer = null;
                                    }
                                }
                            }
                        }, delay);

                        // }

                    } //end of Build version check
                }

                return 1;
            } catch (Exception e) {
                e.printStackTrace();
                return 0;
            }
        }
        //  }
        return 0;
    }





    public static double distFrom(double lat1, double lng1, double lat2, double lng2) {
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












    @Override
    public void onClick(View v) {
        if (v == change_map_options) {
                /*
                Changing Map options on button click To MAP_TYPE_NORMAL,MAP_TYPE_SATELLITE,MAP_TYPE_TERRAIN,MAP_TYPE_HYBRID
                 */

            PopupMenu popup = new PopupMenu(getContext(), change_map_options);
            //Inflating the Popup using xml file
            popup.getMenuInflater()
                    .inflate(R.menu.popup_menu, popup.getMenu());
            //registering popup with OnMenuItemClickListener
            popup.setOnMenuItemClickListener(new PopupMenu.OnMenuItemClickListener() {
                public boolean onMenuItemClick(MenuItem item) {
                    int itemId = item.getItemId();
                    if (itemId == R.id.slot1) {
                        if (mMap != null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_NORMAL);
                            //  Toast.makeText(getContext(), "NORMAL MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    } else if (itemId == R.id.slot2) {
                        if (mMap != null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_SATELLITE);
                            //  Toast.makeText(getContext(), "SATELLITE MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    } else if (itemId == R.id.slot3) {
                        if (mMap != null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_TERRAIN);
                            // Toast.makeText(getContext(), "TERRAIN MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    } else if (itemId == R.id.slot4) {
                        if (mMap != null) {
                            mMap.setMapType(GoogleMap.MAP_TYPE_HYBRID);
                            //  Toast.makeText(getContext(), "HYBRID MAP ENABLED", Toast.LENGTH_SHORT).show();
                        }
                        return true;
                    }
                    return true;
                }
            });
            popup.show();
        } else if (v == re_center) {
                /*
                Recenter Button if map enabled and location enabled get location from map and update map position and
                recenter to  the position captured
                 */
            mMap.setMyLocationEnabled(true);
            if (mPositionMarker != null) {
                LatLng myLocation = null;
                myLocation = mPositionMarker.getPosition();
                int height = 0;
                if (getView() != null) {
                    height = getView().getMeasuredHeight();
                }
                mMap.moveCamera(CameraUpdateFactory.newLatLng(myLocation));
                mMap.animateCamera(CameraUpdateFactory.zoomTo(18));
            }
        } else if (v == submit) {
            if (!dynamic_changeValue.getText().toString().isEmpty()) {
                int val = Integer.parseInt(dynamic_changeValue.getText().toString());
                routeDeviationDistance = val;
                Log.e("Route Deviation Buffer", " Deviation Buffer Test---- " + routeDeviationDistance);
            } else {
                routeDeviationDistance = 10;
            }
        }
    }

    private void sendData(String comm, int AlertType) {
        //comm=time.toString();
        if (comm != null) {
            //  Log.e("SendData", "SendData ------- " + comm + "AlertType" + AlertType);
            Callback.communicate(comm, AlertType);
        } else {

        }

    }

    public void GetRouteFromDBPlotOnMap(String FeatureResponse) {
        String delQuery = "DELETE  FROM " + EdgeDataT.TABLE_NAME;
        // sqlHandler.executeQuery(delQuery);
        JSONObject jsonObject = null;
        try {
            if (FeatureResponse != null) {
                jsonObject = new JSONObject(FeatureResponse);
                String ID = String.valueOf(jsonObject.get("$id"));
                String Status = jsonObject.getString("Status");
                double TotalDistance = jsonObject.getDouble("TotalDistance");
                TotalDistanceInMTS = TotalDistance * 100000;
                JSONArray jSonRoutes = new JSONArray(jsonObject.getString("Route"));
//                PolylineOptions polylineOptions = new PolylineOptions();
                convertedPoints = new ArrayList<LatLng>();

                if (jSonRoutes.length() > 0) {
                    messageContainer.clear();
                    currentRouteData.clear();
                }

                for (int i = 0; i < jSonRoutes.length(); i++) {
                    points = new ArrayList();

                    List<LatLng> arrayOfCoordinates = new ArrayList<>();

                    JSONObject Routes = new JSONObject(jSonRoutes.get(i).toString());
                    String $id = Routes.getString("$id");
                    String EdgeNo = Routes.getString("EdgeNo");
                    String GeometryText = Routes.getString("GeometryText");
                    String Geometry = Routes.getString("Geometry");
                    JSONObject geometryObject = new JSONObject(Routes.getString("Geometry"));
                    String $id1 = geometryObject.getString("$id");
                    String type = geometryObject.getString("type");
                    String coordinates = geometryObject.getString("coordinates");
                    JSONArray jSonLegs = new JSONArray(geometryObject.getString("coordinates"));
                    for (int j = 0; j < jSonLegs.length(); j++) {
                        points.add(jSonLegs.get(j));
                    }

                    String stPoint = String.valueOf(jSonLegs.get(0));
                    String endPoint = String.valueOf(jSonLegs.get(jSonLegs.length() - 1));

                    stPoint = stPoint.replace("[", "");
                    stPoint = stPoint.replace("]", "");
                    String[] firstPoint = stPoint.split(",");
                    Double stPointLat = Double.valueOf(firstPoint[0]);
                    Double stPointLongi = Double.valueOf(firstPoint[1]);
                    LatLng stVertex = new LatLng(stPointLongi, stPointLat);

                    endPoint = endPoint.replace("[", "");
                    endPoint = endPoint.replace("]", "");
                    String[] secondPoint = endPoint.split(",");
                    Double endPointLat = Double.valueOf(secondPoint[0]);
                    Double endPointLongi = Double.valueOf(secondPoint[1]);
                    LatLng endVertex = new LatLng(endPointLongi, endPointLat);


                    double distance = showDistance(stVertex, endVertex);
                    String distanceInKM = String.valueOf(distance / 1000);
                    StringBuilder query = new StringBuilder("INSERT INTO ");
                    query.append(EdgeDataT.TABLE_NAME).append("(edgeNo,distanceInVertex,startPoint,allPoints,geometryText,endPoint) values (")
                            .append("'").append(EdgeNo).append("',")
                            .append("'").append(distanceInKM).append("',")
                            // .append("'").append(String.valueOf(TotalDistanceInMTS)).append("',")
                            .append("'").append(jSonLegs.get(0)).append("',")
                            .append("'").append(points).append("',")
                            .append("'").append(GeometryText).append("',")
                            .append("'").append(jSonLegs.get(jSonLegs.length() - 1)).append("')");
                    //sqlHandler.executeQuery(query.toString());
                    //sqlHandler.closeDataBaseConnection();

                    for (int p = 0; p < points.size(); p++) {
                        String listItem = points.get(p).toString();
                        listItem = listItem.replace("[", "");
                        listItem = listItem.replace("]", "");
                        String[] subListItem = listItem.split(",");
                        Double y = Double.valueOf(subListItem[0]);
                        Double x = Double.valueOf(subListItem[1]);
                        StringBuilder sb = new StringBuilder();
                        LatLng latLng = new LatLng(x, y);
                        convertedPoints.add(latLng);

                        arrayOfCoordinates.add(new LatLng(x, y));
                    }
                    Log.e("convertedPoints", " convertedPoints------ " + convertedPoints.size());

                    // 55.065312867000046, 24.977084458000036
//                    MarkerOptions markerOptions = new MarkerOptions();
//                    for (int k = 0; k < convertedPoints.size(); k++) {
//                        if (polylineOptions != null && mMap != null) {
//                            markerOptions.position(convertedPoints.get(k));
//                            markerOptions.title("Position");
//                        }
//                    }

                    currentRouteData.addAll(cloneCoordinates(arrayOfCoordinates));
                    //add message
                    messageContainer.add(new RouteMessage(GeometryText, arrayOfCoordinates));
                }

                // will remove the duplicates remove that object
                removeDuplicatesRouteDeviated(currentRouteData);

                SourceNode = cloneCoordinate(currentRouteData.get(0));
                DestinationNode = cloneCoordinate(currentRouteData.get(currentRouteData.size() - 1));

                // DRAWING THE CURRENT ROUTE
                currentPolylineOptions.addAll(cloneCoordinates(convertedPoints));
                currentPolylineOptions.color(NSGMapFragment.CURRENT_ROUTE_COLOR).width(NSGMapFragment.CURRENT_ROUTE_WIDTH);
                currentPolylineGraphics = mMap.addPolyline(currentPolylineOptions);
                // polyline.setJointType(JointType.ROUND);
            }
        } catch (JSONException e) {
            e.printStackTrace();
        }

    }


    private void removeDuplicatesRouteDeviated(List<LatLng> listOfPoint) {
        List<LatLng> newData = removeDuplicates(listOfPoint);
        if (newData.size() < listOfPoint.size()) {
            listOfPoint.clear();
            listOfPoint.addAll(newData);
        }
    }


    // modified by SKC
    private List<LatLng> removeDuplicates(List<LatLng> pointList) {

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
    private void drawMarkerWithCircle(LatLng gpsPosition, double radius) {
        CircleOptions circleOptions = new CircleOptions().center(gpsPosition).radius(radius).fillColor(Color.parseColor("#2271cce7")).strokeColor(Color.parseColor("#2271cce7")).strokeWidth(3);
        mCircle = mMap.addCircle(circleOptions);

    }

    private BitmapDescriptor bitmapDescriptorFromVector(Context context, int vectorResId) {
        Drawable vectorDrawable = ContextCompat.getDrawable(context, vectorResId);
        vectorDrawable.setBounds(10, 0, vectorDrawable.getIntrinsicWidth(), vectorDrawable.getIntrinsicHeight());
        Bitmap bitmap = Bitmap.createBitmap(vectorDrawable.getIntrinsicWidth(), vectorDrawable.getIntrinsicHeight(), Bitmap.Config.ARGB_8888);
        Canvas canvas = new Canvas(bitmap);
        vectorDrawable.draw(canvas);
        return BitmapDescriptorFactory.fromBitmap(bitmap);
    }
    private boolean checkPermission() {
        int result = ContextCompat.checkSelfPermission(getContext(), ACCESS_FINE_LOCATION);
        int result1 = ContextCompat.checkSelfPermission(getContext(), READ_EXTERNAL_STORAGE);

        return true;
    }

    public void writeLogFile() {
        if (isExternalStorageWritable()) {

            File appDirectory = new File(Environment.getExternalStorageDirectory() + "/RORO_AppLogs");
            File logDirectory = new File(appDirectory + "/log");
            File logFile = new File(logDirectory, "RORO_Log" + System.currentTimeMillis() + ".txt");

            // create app folder
            if (!appDirectory.exists()) {
                appDirectory.mkdir();
            }

            // create log folder
            if (!logDirectory.exists()) {
                logDirectory.mkdir();
            }

            // clear the previous logcat and then write the new one to the file
            try {
                Process process = Runtime.getRuntime().exec("logcat -c");
                process = Runtime.getRuntime().exec("logcat -f " + logFile);
            } catch (IOException e) {
                e.printStackTrace();
            }

        } else if (isExternalStorageReadable()) {
            // only readable
        } else {
            // not accessible
        }
    }
    public boolean isExternalStorageWritable() {
        String state = Environment.getExternalStorageState();
        if (Environment.MEDIA_MOUNTED.equals(state)) {
            return true;
        }
        return false;
    }

    /* Checks if external storage is available to at least read */
    public boolean isExternalStorageReadable() {
        String state = Environment.getExternalStorageState();
        if (Environment.MEDIA_MOUNTED.equals(state) ||
                Environment.MEDIA_MOUNTED_READ_ONLY.equals(state)) {
            return true;
        }
        return false;
    }

    private void requestPermission() {

        ActivityCompat.requestPermissions(getActivity(), new String[]{ACCESS_FINE_LOCATION, READ_EXTERNAL_STORAGE}, PERMISSION_REQUEST_CODE);

    }


    @Override
    public void onRequestPermissionsResult(int requestCode, @NonNull String[] permissions, @NonNull int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        switch (requestCode) {
            case PERMISSION_REQUEST_CODE: {
                if (grantResults.length > 0) {

                    locationAccepted = grantResults[0] == PackageManager.PERMISSION_GRANTED;
                    boolean storageAccepted = grantResults[1] == PackageManager.PERMISSION_GRANTED;

                    if (locationAccepted && storageAccepted) {
                        Toast.makeText(getContext(), "Permission Granted,.", Toast.LENGTH_LONG).show();
                    } else {
                        // Toast.makeText(this, "Permission Denied, You cannot access location data and camera.", Snackbar.LENGTH_LONG).show();

                        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                            if (shouldShowRequestPermissionRationale(ACCESS_FINE_LOCATION)) {
                                AlertDialog.Builder builder = new AlertDialog.Builder(getContext());
                                builder.setMessage("Look at this dialog!")
                                        .setCancelable(false)
                                        .setPositiveButton("OK", new DialogInterface.OnClickListener() {
                                            public void onClick(DialogInterface dialog, int id) {
                                                if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.M) {
                                                    requestPermissions(new String[]{ACCESS_FINE_LOCATION, READ_EXTERNAL_STORAGE},
                                                            PERMISSION_REQUEST_CODE);
                                                }
                                            }
                                        });
                                AlertDialog alert = builder.create();
                                alert.show();

                                return;
                            }
                        }

                    }
                }
            }
            break;
            case 1000: {
                // If request is cancelled, the result arrays are empty.
                if (grantResults.length > 0
                        && grantResults[0] == PackageManager.PERMISSION_GRANTED) {

                    if (isContinue) {
                        mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                    } else {
                        mFusedLocationClient.getLastLocation().addOnSuccessListener(getActivity(), new OnSuccessListener<Location>() {
                            @Override
                            public void onSuccess(Location location) {
                                if (location != null) {
                                    wayLatitude = location.getLatitude();
                                    wayLongitude = location.getLongitude();
                                    // Log.v("APP DATA","LAT VALUE"+wayLatitude);
                                    // Log.v("APP DATA","LAT VALUE"+wayLongitude);
                                    //txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));


                                } else {
                                    mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                                }
                            }
                        });
                    }
                } else {
                    Toast.makeText(getContext(), "Permission denied", Toast.LENGTH_SHORT).show();
                }
                break;
            }
        }
    }


    private LatLng getLocation() {

        if (isContinue) {
            // Log.v("APP DATA","checking IF ic continue "+isContinue);
            if (mFusedLocationClient != null && locationRequest != null && locationCallback != null) {
                mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
            }
            // Log.v("APP DATA","checking IF ");
            mFusedLocationClient.getLastLocation().addOnSuccessListener(getActivity(), new OnSuccessListener<Location>() {
                @Override
                public void onSuccess(Location location) {
                    //  Log.v("APP DATA","LOCATION NULL");
                    //   Log.v("APP DATA","checking else ic continue "+isContinue);
                    if (location != null) {
                        wayLatitude = location.getLatitude();
                        wayLongitude = location.getLongitude();
                        currentGPSPosition = new LatLng(wayLatitude, wayLongitude);
                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK GET LOCATION METHOD LAT-- 09-JAN-2021"+wayLatitude);

                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK GET LOCATION METHOD LONG-- 09-JAN-2021"+wayLongitude);

                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK GET LOCATION METHOD -- 09-JAN-2021"+currentGPSPosition);


                        //just for trail
                        String S = String.valueOf(location.getLatitude());
                        // Log.v("APP DATA",""+S);
                        Log.e("latitude FROM SERVICE",location.getLatitude()+"");
                        Log.e("longitude FROM SERVICE",location.getLongitude()+"");
                        //txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));

                        Log.d("TAG", "location DATA ........" + "CURRENT GPS POSITION : " + wayLatitude + "," + wayLongitude);
                    } else {
                        mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                    }
                }
            });


        } else {
            mFusedLocationClient.getLastLocation().addOnSuccessListener(getActivity(), new OnSuccessListener<Location>() {
                @Override
                public void onSuccess(Location location) {
                    //  Log.v("APP DATA","LOCATION NULL");
                    //   Log.v("APP DATA","checking else ic continue "+isContinue);
                    if (location != null) {
                        wayLatitude = location.getLatitude();
                        wayLongitude = location.getLongitude();
                        currentGPSPosition = new LatLng(wayLatitude, wayLongitude);
                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK GET LOCATION METHOD LAT-- 09-JAN-2021"+wayLatitude);

                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK GET LOCATION METHOD LONG-- 09-JAN-2021"+wayLongitude);

                        Log.e("LOCATION CALLBACK","LOCATION CALLBACK GET LOCATION METHOD -- 09-JAN-2021"+currentGPSPosition);


                        //just for trail
                        String S = String.valueOf(location.getLatitude());
                        // Log.v("APP DATA",""+S);
                         Log.e("latitude FROM SERVICE",location.getLatitude()+"");
                         Log.e("longitude FROM SERVICE",location.getLongitude()+"");
                        //txtLocation.setText(String.format(Locale.US, "%s - %s", wayLatitude, wayLongitude));

                        Log.d("TAG", "location DATA ........" + "CURRENT GPS POSITION : " + wayLatitude + "," + wayLongitude);
                    } else {
                        mFusedLocationClient.requestLocationUpdates(locationRequest, locationCallback, null);
                    }
                }
            });
        }
        //  }
        Log.e("APP DATA ", "START NAVI CURRENT GPS POSITION 09-JAN-2021 ----" + currentGpsPosition);

        return currentGPSPosition;
    }

    @Override
    public void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (resultCode == Activity.RESULT_OK) {
            if (requestCode == AppConstants.GPS_REQUEST) {
//                isGPS = true; // flag maintain before get location
            }
        }
    }



    private double showDistance(LatLng latlng1, LatLng latLng2) {
        double distance = SphericalUtil.computeDistanceBetween(latlng1, latLng2);
        return distance;
    }


    public LatLng cloneCoordinate(LatLng point) {
        if (point == null) return null;
        return new LatLng(point.latitude, point.longitude);
    }

    public List<LatLng> cloneCoordinates(List<LatLng> points) {
        List<LatLng> pointReversed = new ArrayList<>();
        for (LatLng point : points) {
            pointReversed.add(cloneCoordinate(point));
        }
        return pointReversed;
        // return points.stream().map( elem -> reverseCoordinate(elem)).collect(Collectors.toList());
        //return new LatLng(point.longitude, point.latitude)
    }

    public double calculateDistanceAlongLine(List<LatLng> polyline, LatLng from, LatLng to) {
        double distanceA = calculateDistanceAlongLineFromStart(polyline, from);
        double distanceB = calculateDistanceAlongLineFromStart(polyline, to);
        return (distanceB - distanceA);
    }

    private double calculateDistanceAlongLineFromStart(List<LatLng> polyline, LatLng position) {
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

    private boolean isSameCoordinate(LatLng pointA, LatLng pointB) {

        if (pointA == null || pointB == null) {
            return false;
        }

        String latPointA = truncateDecimal(pointA.latitude, 8).toString();
        String lngPointA = truncateDecimal(pointA.longitude, 8).toString();

        String latPointB = truncateDecimal(pointB.latitude, 8).toString();
        String lngPointB = truncateDecimal(pointB.longitude, 8).toString();

        return latPointA.equals(latPointB) && lngPointA.equals(lngPointB);
    }

    public BigDecimal truncateDecimal(double x, int numberOfDecimals) {
        if (x > 0) {
            return new BigDecimal(String.valueOf(x)).setScale(numberOfDecimals, BigDecimal.ROUND_FLOOR);
        } else {
            return new BigDecimal(String.valueOf(x)).setScale(numberOfDecimals, BigDecimal.ROUND_CEILING);
        }
    }

    public List<List<LatLng>> splitLineByPoint(List<LatLng> polyline, LatLng position) {

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


    private LatLng findNearestPoint(final LatLng p, final LatLng start, final LatLng end) {
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

    public LatLng findNearestPointOnLine(List<LatLng> polyline, LatLng position) {

        LatLng nearestPoint = null;
        List<LatLng> nearestEdge = new ArrayList<>();

        if (polyline.size() < 2) {
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


    public String displayNavigationMessage(final LatLng currentPosition) {

        String message = null;
        long distanceToTravel = 0l;

        LatLng perpendicularPoint = findNearestPointOnLine(currentRouteData, currentPosition);
        RouteMessage routeMessage = null;
        for (int i = 0; i < messageContainer.size(); i++) {
            routeMessage = messageContainer.get(i);
            if (PolyUtil.isLocationOnPath(perpendicularPoint, routeMessage.getLine(), false)) {
                break;
            }
        }

        if (routeMessage == null) {
            return message;
        }

        List<List<LatLng>> splittedLine = splitLineByPoint(routeMessage.getLine(), perpendicularPoint);

        if (splittedLine.size() == 2) {
            distanceToTravel = (long) SphericalUtil.computeLength(splittedLine.get(1));
            message = routeMessage.getMessage();
        }

        //for log only

        if (distanceToTravel == 0) {
            Log.e("routeMessage-", "currentRouteData: " + currentRouteData.toString());
            Log.e("routeMessage-", "currentPosition: " + currentPosition.toString());
            Log.e("routeMessage-", "perpendicularPoint: " + perpendicularPoint.toString());

            Log.e("routeMessage-", "message: " + routeMessage.getMessage());
            Log.e("routeMessage-", "line: " + routeMessage.getLine().toString());

            Log.e("routeMessage-", "splittedLine: " + splittedLine.toString());
        }


        if (message != null && !message.isEmpty() && distanceToTravel > 0) {
            String fullMessage = message + " " + distanceToTravel + " meters";
            if (getActivity() != null) {
                int speechStatus = textToSpeech.speak(fullMessage, TextToSpeech.QUEUE_FLUSH, null);
                if (speechStatus == TextToSpeech.ERROR) {
                    // Log.e("TTS", "Error in converting Text to Speech!");
                }

                LayoutInflater inflater1 = getActivity().getLayoutInflater();
                @SuppressLint("WrongViewCast") final View layout = inflater1.inflate(R.layout.custom_toast, (ViewGroup) getActivity().findViewById(R.id.textView_toast));
                TextView text = (TextView) layout.findViewById(R.id.textView_toast);

                text.setText(fullMessage);
                ImageView image = (ImageView) layout.findViewById(R.id.image_toast);
                if (message.contains("Take Right")) {
                    image.setImageResource(R.drawable.direction_right);
                } else if (message.contains("Take Left")) {
                    image.setImageResource(R.drawable.direction_left);
                }
                if (getActivity() != null) {
                    new Handler(Looper.getMainLooper()).post(new Runnable() {
                        @Override
                        public void run() {
                            Toast toast = new Toast(getActivity().getApplicationContext());
                            toast.setDuration(Toast.LENGTH_LONG);
                            toast.setGravity(Gravity.TOP | Gravity.CENTER_HORIZONTAL, 0, 0);
                            toast.setGravity(Gravity.TOP, 0, 130);
                            toast.setView(layout);
                            toast.show();
                        }
                    });
                }
            }
        }

        return message;
    }


    public void calculateETA(long startTimestamp, LatLng currentPosition, List<LatLng> routeLine) {

        if (routeLine.size() == 0 || startTimestamp == 0 || nearlyFirstGPSPosition == null) {
            return;
        }

        double vehicleSpeed = 0d;

        int timeTakenTillNow = (int) ((System.currentTimeMillis() - startTimestamp) / 1000); // in seconds

        double totalDistance = SphericalUtil.computeLength(routeLine);
//        int estimatedTime = (int) (((totalDistance / 1000) / vehicleSpeed) * 3600);   // in seconds
        List<List<LatLng>> splitRoute = splitLineByPoint(routeLine, currentPosition);

        int etaElapsed = 0;
        double remainingDistance = 0d;
        double minimumSpeed = (NSGMapFragment.MINIMUM_VEHICLE_SPEED * 1000d) / 3600d;
        if (splitRoute.size() == 2) {
            remainingDistance = SphericalUtil.computeLength(splitRoute.get(1));
            double travelledDistance = SphericalUtil.computeLength(splitRoute.get(0));

            travelledDistance = travelledDistance - calculateDistanceAlongLineFromStart(splitRoute.get(0), nearlyFirstGPSPosition);

            if (timeTakenTillNow > 0 && travelledDistance > 0) {
                vehicleSpeed = travelledDistance / timeTakenTillNow;
            }

            if (vehicleSpeed > minimumSpeed) {
                estimatedRemainingTime = (int) (remainingDistance / vehicleSpeed);   // in seconds
            } else {
                estimatedRemainingTime = (int) (remainingDistance / minimumSpeed);   // in seconds
            }
        }

        if (timeTakenTillNow > estimatedTimeInSeconds) {
            etaElapsed = timeTakenTillNow - estimatedTimeInSeconds;
        }


//        time.append("Distance : ").append(totalDistance + " Meters ")
//                .append("::").append("total predicted time : ")
//                .append(estimatedTimeInSeconds + " SEC ")
//                .append("::").append(" Distance To Travel : ")
//                .append(estimatedRemainingTime + "Sec").append("::")
//                .append("Elapsed Time : ").append(etaElapsed).append("::")
//                .append("currentGpsPosition : ").append(currentPosition).append("\n");

        StringBuilder timeTmp = new StringBuilder();
        timeTmp.append("predicted time : ")
                .append(estimatedTimeInSeconds + " SEC ").append("::")
                .append("Elapsed time: ").append(etaElapsed).append("::")
                .append("timeTakenTillNow: ").append(timeTakenTillNow).append("::")
                .append("estimatedRemainingTime: ").append(estimatedRemainingTime).append("::")
                .append("totalDistance: ").append(totalDistance).append("::")
                .append("remainingDistance: ").append(remainingDistance).append("::")
                .append("vehicleSpeed (mtr./sec): ").append(vehicleSpeed).append("::");
        if (vehicleSpeed > minimumSpeed) {
            timeTmp.append("used vehicleSpeed (mtr./sec): ").append(vehicleSpeed).append("::");
        } else {
            timeTmp.append("used vehicleSpeed (mtr./sec): ").append(minimumSpeed).append("::");
        }
        timeTmp.append("currentGpsPosition : ").append(currentPosition.toString()).append("\n");


        Log.e("ETA", "ETA ALERT ---- " + timeTmp);

        Log.e("ETA", "currentPosition ---- " + reverseCoordinate(currentPosition).toString());
        Log.e("ETA", "routeLine ---- " + reverseCoordinates(routeLine).toString());

        for (List<LatLng> elem : splitRoute) {
            Log.e("ETA", "splitRoute ---- " + reverseCoordinates(elem).toString());
        }
        Log.e("ETA", "vehicleSpeed ---- " + vehicleSpeed);
        Log.e("ETA", "timeTakenTillNow ---- " + timeTakenTillNow);

        sendData(timeTmp.toString(), MapEvents.ALERTTYPE_2);

        if (etaElapsed > 0 && !isETACrossed) {
            // send eta message only one time
            isETACrossed = true;
            sendData(timeTmp.toString(), MapEvents.ALERTTYPE_7);
        }

    }

    public LatLng reverseCoordinate(LatLng point) {
        return new LatLng(point.longitude, point.latitude);
    }

    public List<LatLng> reverseCoordinates(List<LatLng> points) {
        List<LatLng> pointReversed = new ArrayList<>();
        for (LatLng point : points) {
            pointReversed.add(reverseCoordinate(point));
        }
        return pointReversed;
        // return points.stream().map( elem -> reverseCoordinate(elem)).collect(Collectors.toList());
        //return new LatLng(point.longitude, point.latitude)
    }
}
