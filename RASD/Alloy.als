--@@@@@@@@@@@@ SIG AND FACT @@@@@@@@@@@@@@

abstract sig Person{
    email: one Email
}
sig Email{}
--each person has different email
fact uniquePerson{all p1,p2:Person|(p1!=p2)=>p1.email!=p2.email}
--each email has user
fact EmailPerson{Person.email=Email}

--------------------------------------------------------PLATE
sig Plate{}
--each plate has a car
fact PlateCar{Car.plate=Plate}
--each car has different plate
fact uniquePlate{all c1,c2:Car | (c1!=c2) => c1.plate!=c2.plate}

--------------------------------------------------------COORDINATE
sig Coordinate{
    area: one Area,
    spa: one ServicePA,
}
fact {Coordinate=User.coordinate+ChargingTower.is+Car.is}

--------------------------------------------------------AREA
enum Area{SafeArea,noSafeArea,OutsideArea}

--------------------------------------------------------STAFF
sig Staff extends Person{
    handle: set HelpRequest
}
--------------------------------------------------------USER
sig User extends Person{
    has:lone TemporaryBill,
    ask: lone HelpRequest,
    coordinate: one Coordinate
}
--different users have different reservation
fact UniqueReservation{no u1,u2:User | u1!=u2 and u1.has=u2.has}
--each user has different coordinate
fact UserUniquePosition{ no u1,u2:User | u1!=u2 and u1.coordinate=u2.coordinate}

--------------------------------------------------------CAR
sig Car{
    plate: one Plate,
    state: one Tag,
    is: one Coordinate,
    tb: lone TemporaryBill
}

--available cars are inside The Area
fact AvailableIsInside{no c:Car | c.state=Available and c.is.area=OutsideArea}
--each car has different coordinate
fact CarCoord{no c1,c2:Car | c1!=c2 and c1.is=c2.is}
--all available and reserved cars  are in safe
fact AvCarSafe{all c:Car | (c.state=Available or c.state=Reserved) => c.is.area=SafeArea}
--all pause cars are in safe or outside the area
fact PauseCarSafeOut{all c:Car | (c.state=Pause) => ((c.is.area=SafeArea and c.is.spa=false ) or c.is.area=OutsideArea)}
--if car position is in user position, his car is in use
fact UserUseCar{all u:User | all c:Car | u.coordinate=c.is iff (c.state=In_use and c.tb=u.has)}
--each use or pause car has reservation

----QUI PROBLEMI
fact TBcar{ no c:Car| (c.state=Available or c.state=Out_of_power)  and #c.tb=1}
--each available or oop car has reservation
fact noTBcar{ no c:Car| (c.state=In_use or c.state=Pause or c.state=Reserved) and #c.tb=0}

------------------------------------------------------TEMPORARY BILL
enum Tag{Available,Pause,Out_of_power,In_use,Reserved}
sig TemporaryBill{
  time: Int, --minute
  bill:one Int
}{
  time>0
} 
fact UniqueReservation2{no c1,c2:Car | c1!=c2 and c1.tb=c2.tb}
--tempBill 
fact TempBillUser{User.has=TemporaryBill}
fact BilllFee{ all c:Car | c.state=Reserved => (c.tb.bill=0)}
fact BilllFee2{ all c:Car | (c.state=In_use or c.state=Pause) => (c.tb.bill=mul[c.tb.time,1])} -- 1eur  per minute fee

-------------------------------------------------------HELP REQUEST
sig HelpRequest{}
--help request 
fact HelpRequestUser{User.ask=HelpRequest}
fact HelpRequestStaff{Staff.handle in HelpRequest}
fact UniqueHelpRequest{no u1,u2:User | u1!=u2 and u1.ask=u2.ask}

-------------------------------------------------------SPA
enum ServicePA{true,false}
sig SPA{
    parking:some ChargingTower
}
--spa is always in safe area
fact SPASafe{all c:Coordinate| c.spa=true => c.area=SafeArea}

------------------------------------------------------CHARGING TOWER
sig ChargingTower{
    isFree: one SpotFree,
    is:one Coordinate
}
enum SpotFree{True,False}
fact UniqueCoordinateCT{no c1,c2:ChargingTower | c1!=c2 and c1.is=c2.is}
--every chargingTower has in a SPA
fact chargingTowerSPA{all c:ChargingTower | one s:SPA | c in s.parking}
--all charging towers are in SPA (SCONTATO?)
fact ChargingTower{all c:ChargingTower | c.is.spa=true}
fact{all coo:Coordinate|one crg:ChargingTower|coo.spa=true implies crg.is=coo}
--if car has the same coordinate of chargTow charg isFree=False
fact ChargingTowerBusyCarCharging{all car:Car  | no c:ChargingTower | car.is=c.is and c.isFree=True}
fact ChargingTowerBusyCarCharging2{all c:ChargingTower | some car:Car  |  c.isFree=False and car.is=c.is}


--@@@@@@@@@@@@@@   ASSERTS   @@@@@@@@@@@@@@@@@

--A car can have a tb only if is in Pause, In_use or Reserved
assert BillForPauseOrUseOrReserved{ all  car:Car| some  t:TemporaryBill |(car.state=Pause or car.state=In_use or car.state=Reserved) implies car.tb=t}
--all oop or available cars are not linked to tbills
assert BillForPauseOrUseOrReserved2{ all car:Car |no t:TemporaryBill | car.tb=t and (car.state=Out_of_power or car.state=Available) }
--available cars are in safe area
assert AvailableOnlyInSafeArea{all c:Car | c.state=Available implies c.is.area=SafeArea}
--free tower has not same coordinate of a car
assert NoCarInSpaTowerFree{all crg:ChargingTower | no car:Car | car.is=crg.is and crg.isFree=True}
--if car is in chargintower, tower is not free
assert CarInSpaTowerBusy {all crg:ChargingTower| all car:Car| crg.is=car.is implies crg.isFree=False}
--doesnt exist available car outside the area
assert NoAvailableCarOutOfTheArea{no c:Car | c.state=Available and c.is.area=OutsideArea}
--Bill remains 0 if car is Reserved
assert BillReserved{all c:Car|no t:TemporaryBill | c.tb=t and c.state=Reserved and t.bill!=0}
--to this abstract level world bill cannot be 0 if car is in use or in pause 
assert BillOtherwise{all c:Car|no t:TemporaryBill | (c.state=In_use or c.state=Pause)and c.tb=t and t.bill=0}

--@@@@@@@@@@@@@@    PREDICATE   @@@@@@@@@@@@@@@

pred show{
#Car>2
#User>1
#Staff>0
#SPA>1
#ChargingTower>#SPA
}

pred show2{
(some c:Car|c.state=Available)
(some c2:Car|c2.state=Pause)
(some c3:Car|c3.state=Reserved)
--(some c4:Car|c4.state=In_use) and
(some c5:Car|c5.state=Out_of_power) 
}

pred HelpRequest(u:User, s1,s2:Staff){
	u.ask not in s1.handle implies s2.handle=s1.handle+u.ask
}

pred askForHelp(u:User, s1,s2:Staff){
	HelpRequest[u,s1,s2]
	#s2.handle>0
}

--@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

check NoAvailableCarOutOfTheArea
check CarInSpaTowerBusy
check BillForPauseOrUseOrReserved
check BillForPauseOrUseOrReserved2
check NoCarInSpaTowerFree
check AvailableOnlyInSafeArea
check BillReserved
check BillOtherwise

run askForHelp
run show2 for 10
run show
