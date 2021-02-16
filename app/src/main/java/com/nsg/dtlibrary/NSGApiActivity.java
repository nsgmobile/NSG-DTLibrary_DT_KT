package com.nsg.dtlibrary;

import android.app.AlertDialog;
import android.content.DialogInterface;
import android.os.Bundle;
import android.os.Environment;
import android.sax.StartElementListener;
import android.util.Log;
import android.view.View;
import android.widget.Button;
import android.widget.TextView;


import com.nsg.nsgdtlibrary.Classes.util.NSGIMapFragmentActivity;
import com.nsg.nsgdtlibrary.Classes.util.NSGMapFragment;

import java.io.File;

import androidx.fragment.app.FragmentActivity;
import androidx.fragment.app.FragmentManager;
import androidx.fragment.app.FragmentTransaction;

/**
 * Created by sailaja.ch NSGI on 27/09/2019
 */
public class NSGApiActivity extends FragmentActivity implements NSGIMapFragmentActivity.FragmentToActivity, View.OnClickListener {
    private int bufferSize=10;
    private String charlsisNumber;
    private  Button Start,Stop;
    private String jobId="1",routeId;

    //StartNode":"55.0747788313063 24.9888888378752","EndNode":"55.0752064557586 24.9885681420569"

    private String SourcePosition = "55.0747788313063 24.9888888378752";
    private String DestinationPosition = "55.0752064557586 24.9885681420569";
    // 25.26886,55.33279   25.27078,55.3327
    String routeData="{\n" +
            "    \"$id\": \"1\",\n" +
            "    \"Message\": \"Sucess\",\n" +
            "    \"Status\": \"Success\",\n" +
            "    \"TotalDistance\": 0.002561889568,\n" +
            "    \"Route\": [\n" +
            "        {\n" +
            "            \"$id\": \"2\",\n" +
            "            \"EdgeNo\": \"1750\",\n" +
            "            \"GeometryText\": \"Take Left at\",\n" +
            "            \"Geometry\": {\n" +
            "                \"$id\": \"3\",\n" +
            "                \"type\": \"LineString\",\n" +
            "                \"coordinates\": [\n" +
            "                    [\n" +
            "                        55.074807683000074,\n" +
            "                        24.988573621000057\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.074762276000058,\n" +
            "                        24.988534159000039\n" +
            "                    ]\n" +
            "                ]\n" +
            "            }\n" +
            "        },\n" +
            "        {\n" +
            "            \"$id\": \"4\",\n" +
            "            \"EdgeNo\": \"227\",\n" +
            "            \"GeometryText\": \"Take Left at\",\n" +
            "            \"Geometry\": {\n" +
            "                \"$id\": \"5\",\n" +
            "                \"type\": \"LineString\",\n" +
            "                \"coordinates\": [\n" +
            "                    [\n" +
            "                        55.074762276000058,\n" +
            "                        24.988534159000039\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.074573660000055,\n" +
            "                        24.988370235000048\n" +
            "                    ]\n" +
            "                ]\n" +
            "            }\n" +
            "        },\n" +
            "        {\n" +
            "            \"$id\": \"6\",\n" +
            "            \"EdgeNo\": \"683\",\n" +
            "            \"GeometryText\": \"Take Left at\",\n" +
            "            \"Geometry\": {\n" +
            "                \"$id\": \"7\",\n" +
            "                \"type\": \"LineString\",\n" +
            "                \"coordinates\": [\n" +
            "                    [\n" +
            "                        55.074573660000055,\n" +
            "                        24.988370235000048\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.074562880000087,\n" +
            "                        24.988341736000052\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.074556554000083,\n" +
            "                        24.988312147000045\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.074554806000037,\n" +
            "                        24.988282044000073\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.074557670000047,\n" +
            "                        24.988252013000078\n" +
            "                    ]\n" +
            "                ]\n" +
            "            }\n" +
            "        },\n" +
            "        {\n" +
            "            \"$id\": \"8\",\n" +
            "            \"EdgeNo\": \"36\",\n" +
            "            \"GeometryText\": \"Take Left at\",\n" +
            "            \"Geometry\": {\n" +
            "                \"$id\": \"9\",\n" +
            "                \"type\": \"LineString\",\n" +
            "                \"coordinates\": [\n" +
            "                    [\n" +
            "                        55.074557670000047,\n" +
            "                        24.988252013000078\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.07483693000006,\n" +
            "                        24.98798815400005\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075051850000079,\n" +
            "                        24.987784887000089\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075136984000039,\n" +
            "                        24.987704541000085\n" +
            "                    ]\n" +
            "                ]\n" +
            "            }\n" +
            "        },\n" +
            "        {\n" +
            "            \"$id\": \"10\",\n" +
            "            \"EdgeNo\": \"691\",\n" +
            "            \"GeometryText\": \"Take Right at\",\n" +
            "            \"Geometry\": {\n" +
            "                \"$id\": \"11\",\n" +
            "                \"type\": \"LineString\",\n" +
            "                \"coordinates\": [\n" +
            "                    [\n" +
            "                        55.075136984000039,\n" +
            "                        24.987704541000085\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075165876000085,\n" +
            "                        24.987700299000039\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075195140000062,\n" +
            "                        24.987700203000088\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075224065000043,\n" +
            "                        24.987704256000086\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075251946000037,\n" +
            "                        24.987712359000056\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075278105000052,\n" +
            "                        24.987724315000037\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075278105000052,\n" +
            "                        24.987724315000037\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075424316000067,\n" +
            "                        24.987851401000057\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075515274000054,\n" +
            "                        24.987930511000059\n" +
            "                    ]\n" +
            "                ]\n" +
            "            }\n" +
            "        },\n" +
            "        {\n" +
            "            \"$id\": \"12\",\n" +
            "            \"EdgeNo\": \"731\",\n" +
            "            \"GeometryText\": \"Take Right at\",\n" +
            "            \"Geometry\": {\n" +
            "                \"$id\": \"13\",\n" +
            "                \"type\": \"LineString\",\n" +
            "                \"coordinates\": [\n" +
            "                    [\n" +
            "                        55.075515274000054,\n" +
            "                        24.987930511000059\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075521534000075,\n" +
            "                        24.987944715000083\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075525346000063,\n" +
            "                        24.987959622000062\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075526623000087,\n" +
            "                        24.987974884000039\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075525334000076,\n" +
            "                        24.987990145000083\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075521509000055,\n" +
            "                        24.988005050000083\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075515238000037,\n" +
            "                        24.988019249000047\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.075506666000081,\n" +
            "                        24.988032412000052\n" +
            "                    ]\n" +
            "                ]\n" +
            "            }\n" +
            "        },\n" +
            "        {\n" +
            "            \"$id\": \"14\",\n" +
            "            \"EdgeNo\": \"37\",\n" +
            "            \"GeometryText\": \"-\",\n" +
            "            \"Geometry\": {\n" +
            "                \"$id\": \"15\",\n" +
            "                \"type\": \"LineString\",\n" +
            "                \"coordinates\": [\n" +
            "                    [\n" +
            "                        55.0750822742003,\n" +
            "                        24.9884382989051\n" +
            "                    ],\n" +
            "                    [\n" +
            "                        55.074953222000033,\n" +
            "                        24.988561724000078\n" +
            "                    ]\n" +
            "                ]\n" +
            "            }\n" +
            "        }\n" +
            "    ]\n" +
            "}";


private String GeoFenceCordinates="\n" +
        "\n" +
        "\n" +
        "24.980209 55.067516,\n" +
        "24.979489 55.067344,\n" +
        "24.979528 55.066959,\n" +
        "24.980004 55.066765,\n" +
        "24.980520 55.066915,\n" +
        "24.980744 55.067656";
/*
    private String GeoFenceCordinates="\n" +
            "\n" +
            "\n" +
            "24.980209 55.067516,\n" +
            "24.979489 55.067344,\n" +
            "24.979528 55.066959,\n" +
            "24.980004 55.066765,\n" +
            "24.980520 55.066915,\n" +
            "24.980744 55.067656";


    private String SourcePosition = "55.067291 24.978782";
    private String DestinationPosition = "55.067205 24.979878";
    // 25.26886,55.33279   25.27078,55.3327
    String routeData="\n" +
            "\n" +
            "{\"$id\":\"1\",\"Message\":\"Sucess\",\"Status\":\"Success\",\"TotalDistance\":0.00884315523,\"Route\":[{\"$id\":\"2\",\"EdgeNo\":\"102\",\"GeometryText\":\"Take Right \n" +
            "at Shell Trading Middle East Private Limited\",\"Geometry\":{\"$id\":\"3\",\"type\":\"LineString\",\"coordinates\":[[55.06727997182,24.9787947412557],\n" +
            "[55.067020892000073,24.978570495000042],[55.066790925000078,24.978370131000077],[55.066620030000081,24.978221328000075],\n" +
            "[55.06650374700007,24.97812037500006],[55.066452143000049,24.978075252000053],[55.066388841000048,24.978020054000069],\n" +
            "[55.066216137000083,24.977870199000051],[55.06598632500004,24.97767018400009],[55.065755946000081,24.977470103000087],\n" +
            "[55.065526233000071,24.977270178000083],[55.065312867000046,24.977084458000036]]}},{\"$id\":\"4\",\"EdgeNo\":\"1334\",\"GeometryText\":\"Take Right \n" +
            "at\",\"Geometry\":{\"$id\":\"5\",\"type\":\"LineString\",\"coordinates\":[[55.065312867000046,24.977084458000036],[55.065287629000068,24.977076221000061],\n" +
            "[55.065261227000065,24.97707199000007],[55.065234420000081,24.97707188600009],[55.065207979000036,24.977075912000089],\n" +
            "[55.065182665000066,24.97708395300009],[55.065159206000033,24.977095778000091],[55.065138276000084,24.977111045000072],\n" +
            "[55.065138276000084,24.977111045000072],[55.065120166000042,24.977128114000038],[55.064756250000073,24.977475793000053],\n" +
            "[55.064379641000073,24.977835331000051],[55.064249201000052,24.977960644000063],[55.064249201000052,24.977960644000063],\n" +
            "[55.064238539000087,24.977972603000069],[55.064230288000033,24.977986052000062],[55.064224693000085,24.978000592000058],\n" +
            "[55.064221918000044,24.978015793000054],[55.064222048000033,24.978031201000078],[55.064222048000033,24.978031201000078],\n" +
            "[55.064387059000069,24.978174369000044],[55.064439134000054,24.978219639000088],[55.064439134000054,24.978219639000088],\n" +
            "[55.064525820000085,24.978294996000045],[55.064525820000085,24.978294996000045],[55.064649532000033,24.978402540000047],\n" +
            "[55.06498055600008,24.978690915000072],[55.06498055600008,24.978690915000072],[55.065164137000068,24.978850842000043],\n" +
            "[55.065338824000037,24.979002188000038],[55.065338824000037,24.979002188000038],[55.065422408000074,24.979074604000061],\n" +
            "[55.065573362000066,24.979205705000084],[55.065573362000066,24.979205705000084],[55.065666012000065,24.979286171000069],\n" +
            "[55.065666012000065,24.979286171000069],[55.065681098000084,24.979299272000048],[55.065938324000058,24.979522600000053],\n" +
            "[55.066002768000033,24.979578645000061],[55.066002768000033,24.979578645000061],[55.066081442000041,24.979647065000051],\n" +
            "[55.066081442000041,24.979647065000051],[55.066110416000072,24.979672262000065],[55.066245676000051,24.979789959000072],\n" +
            "[55.066245676000051,24.979789959000072],[55.06634370900008,24.979875263000054],[55.06634370900008,24.979875263000054],\n" +
            "[55.066752725000072,24.980231166000067],[55.066752725000072,24.980231166000067],[55.066772902000082,24.980240215000038],\n" +
            "[55.066794299000037,24.98024651500009],[55.066816470000049,24.980249936000064],[55.066838951000079,24.980250405000049],\n" +
            "[55.066861270000061,24.980247913000085]]}},{\"$id\":\"6\",\"EdgeNo\":\"443\",\"GeometryText\":\"-\",\"Geometry\":\n" +
            "{\"$id\":\"7\",\"type\":\"LineString\",\"coordinates\":[[55.066861270000061,24.980247913000085],[55.0672260238388,24.9799000715094]]}}]}";

*/
    private TextView tv;
    private String routeDeviatedDT_URL="http://202.53.11.74/dtnavigation/api/routing/routenavigate";
    String BASE_MAP_URL_FORMAT = Environment.getExternalStorageDirectory() + File.separator + "MBTILES" + File.separator + "DubaiBasemap"+".mbtiles";
    private String AuthorisationKey="b3TIz98wORn6daqmthiEu/0cEhQunl3nzV3Fho2qdnknJI25eHMBlhJaGEC8IV80ThpYGSMejy+xa0AkZDJHODweJL/QNr08/Iq7UBDDOwuzSCydNhJSPQBki8IahfUXSmOWE3iT4dq6oI56YoAkSg==";
    String CSVFile_Path= Environment.getExternalStorageDirectory() + File.separator + "MBTILES" + File.separator + "RouteSample"+".txt";
  //  com.nsg.dtlibrary.NavigationProperties properties=new com.nsg.dtlibrary.NavigationProperties();

    NSGIMapFragmentActivity test =new NSGIMapFragmentActivity(BASE_MAP_URL_FORMAT,SourcePosition,DestinationPosition,routeData,bufferSize,routeDeviatedDT_URL,AuthorisationKey,GeoFenceCordinates,false,true);
  // NSGTiledLayerOnMap test = new NSGTiledLayerOnMap(BASE_MAP_URL_FORMAT);
    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.review_map);
        Start =(Button)findViewById(R.id.start);

        Start.setOnClickListener(this);
        Stop=(Button)findViewById(R.id.stop);
        Stop.setOnClickListener(this);

        //Start.setOnClickListener(new  on);



        Bundle NSGIBundle = getIntent().getExtras();
        charlsisNumber = NSGIBundle.getString("charlsisNumber");

        FragmentManager fragmentManager = getSupportFragmentManager();

        FragmentTransaction fragmentTransaction = fragmentManager.beginTransaction();
         if(charlsisNumber.equals("RD1")) {
              fragmentTransaction.add(R.id.map_container, test);
         }else if(charlsisNumber.equals("RD2")) {

        }
        fragmentTransaction.commit();

    }

   // @Override
  //  public String communicate(String comm) {
   //     return null;
  //  }

    @Override
    public String communicate(String comm, int alertType) {
        // Log.e("Started","Started communicate"+ comm +","+alertType);
        if(alertType==MapEvents.ALERTTYPE_6){
            // if alert recieved you can start navigation here
            //test.startNavigation();
           // Log.e("Started","Started "+test.startNavigation());
        }else if(alertType==MapEvents.ALERTTYPE_1){

        }else if(alertType==MapEvents.ALERTTYPE_2){

        }else if(alertType==MapEvents.ALERTTYPE_3){

        }else if(alertType==MapEvents.ALERTTYPE_4) {

            AlertDialog.Builder builder = new AlertDialog.Builder(NSGApiActivity.this, R.style.yourDialog);
            builder.setTitle("Alert");
            builder.setIcon(R.drawable.car_icon_32);
            builder.setMessage("Destination Reached")
                    .setCancelable(false)
                    .setPositiveButton("STOP", new DialogInterface.OnClickListener() {
                        public void onClick(DialogInterface dialog, int id) {
                         //  test.stopNavigation();
                        }
                    });
            AlertDialog alert = builder.create();
            alert.show();



        }else if(alertType==MapEvents.ALERTTYPE_5){

        }
        return comm;
    }
    public void onResume() {
        super.onResume();

    }

    @Override
    public void onClick(View v) {
       if(v.getId() == R.id.start){
          // test.startNavigation();
           Log.e("Started","Started "+test.startNavigation());
       }else if(v.getId() == R.id.stop){
          // test.stopNavigation();
           Log.e("Stopped","Stopped "+test.stopNavigation());
       }
    }
    @Override
    public void onDestroy(){

        Log.e("ON DESTROY"," NSGI API ACTIVITY ");


        if(Start != null) {
            Start.setOnClickListener(null);
            Start = null;
        }

        if(Stop != null) {
            Stop.setOnClickListener(null);
            Stop = null;
        }

        if(test != null) {
            FragmentManager fragmentManager = getSupportFragmentManager();
            FragmentTransaction fragmentTransaction = fragmentManager.beginTransaction();
            fragmentTransaction.remove(test).commitNowAllowingStateLoss();
            test = null;
        }
        super.onDestroy();
    }
}