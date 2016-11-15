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
fact UniqueHandle{no s1,s2:Staff | s1!=s2 and s1.handle=s2.handle}
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


--each car has different coordinate
fact CarCoord{no c1,c2:Car | c1!=c2 and c1.is=c2.is}
--all available and reserved cars  are in safe
fact AvCarSafe{all c:Car | (c.state=Available or c.state=Reserved or c.state=Out_of_power) => c.is.area=SafeArea}
--all pause cars are in safe or outside the area
fact PauseCarSafeOut{no c:Car | (c.state=Pause) and (c.is.area=SafeArea and c.is.spa=true ) }
--if car position is in user position, his car is in use
fact UserUseCar{all u:User | all c:Car | u.coordinate=c.is iff (c.state=In_use and c.tb=u.has)}
--each use or pause car has reservation

----QUI PROBLEMI
fact TBcar{all c:Car| no  t:TemporaryBill | c.state=Available and c.tb=t}
fact TBcar{all c:Car| no  t:TemporaryBill | c.state=Out_of_power and c.tb=t}
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
sig SPA{parking: some ChargingTower}
--spa is always in safe area
fact SPASafe{all c:Coordinate| c.spa=true => c.area=SafeArea}

------------------------------------------------------CHARGING TOWER
sig ChargingTower{
    is:one Coordinate
}
enum SpotFree{True,False}
fact UniqueCoordinateCT{no c1,c2:ChargingTower | c1!=c2 and c1.is=c2.is}
--every chargingTower has in a SPA
fact chargingTowerSPA{all c:ChargingTower | one s:SPA | c in s.parking}
--all charging towers are in SPA 
fact ChargingTower{all c:ChargingTower | c.is.spa=true}
fact{all coo:Coordinate|one crg:ChargingTower|coo.spa=true implies crg.is=coo}

--@@@@@@@@@@@@@@   ASSERTS   @@@@@@@@@@@@@@@@@

--A car can have a tb only if is in Pause, In_use or Reserved
--assert BillForPauseOrUseOrReserved{ all car:Car |(car.state=Pause or car.state=In_use or car.state=Reserved) and #car.tb=1}
--all oop or available cars are not linked to tbills
assert BillForPauseOrUseOrReserved2{ all car:Car |no t:TemporaryBill | car.tb=t and (car.state=Out_of_power or car.state=Available) }
--available cars are in safe area
assert AvailableOnlyInSafeArea{all c:Car | c.state=Available implies c.is.area=SafeArea}
--doesnt exist available car outside the area
assert NoAvailableCarOutOfTheArea{no c:Car | c.state=Available and c.is.area=OutsideArea}
--Bill remains 0 if car is Reserved
assert BillReserved{all c:Car|no t:TemporaryBill | c.tb=t and c.state=Reserved and t.bill!=0}
--to this abstract level world bill cannot be 0 if car is in use or in pause 
assert BillOtherwise{all c:Car|no t:TemporaryBill | (c.state=In_use or c.state=Pause)and c.tb=t and t.bill=0}
--available cars are inside The Area
assert AvailableIsInside{no c:Car | c.state=Available and c.is.area=OutsideArea}

--@@@@@@@@@@@@@@    PREDICATE   @@@@@@@@@@@@@@@

pred show{
#Car>4 
#User>0
#Staff>0
#SPA>1
#ChargingTower>#SPA
}

pred show2{
(some c:Car|c.state=Available)
(some c2:Car|c2.state=Pause)
(some c3:Car| c3.state=Reserved)
(some c4:Car| c4.state=In_use)
(some c5:Car | c5.state=Pause)
}

pred HelpRequest(u:User, s1,s2:Staff){
	u.ask not in s1.handle implies s2.handle=s1.handle+u.ask
}

--@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@

check NoAvailableCarOutOfTheArea
--check BillForPauseOrUseOrReserved
check BillForPauseOrUseOrReserved2
check AvailableIsInside
check AvailableOnlyInSafeArea
check BillReserved
check BillOtherwise

run HelpRequest
run show for 5
run show2 for 10
