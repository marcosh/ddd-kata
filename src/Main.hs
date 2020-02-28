{-# LANGUAGE RankNTypes      #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Main where

import Control.Arrow hiding (loop)
import Control.Lens
import Control.Monad.Trans.State
import Data.Maybe (isNothing, listToMaybe)
import Debug.Trace (trace)

-- Stock

newtype Stock a = Stock
  { _stock :: [a]
  }
  deriving Show

makeLenses ''Stock

stockItems :: [a] -> Stock a
stockItems = Stock

emptyStock :: Stock a
emptyStock = stockItems []

addItemToStock :: a -> Stock a -> Stock a
addItemToStock item (Stock stock) = Stock $ stock ++ [item]

getItemFromStock :: Stock a -> (Maybe a, Stock a)
getItemFromStock (Stock items) = case items of
  []    -> (Nothing, Stock [])
  x:xs -> (Just x  , Stock xs)

isEmpty :: Stock a -> Bool
isEmpty = null . view stock

listContainsOnly :: Eq a => a -> [a] -> Bool
listContainsOnly _       []     = True
listContainsOnly element (x:xs) = element == x && listContainsOnly element xs

containsOnly :: Eq a => a -> Stock a -> Bool
containsOnly element = listContainsOnly element . view stock

-- places

data Place
  = Factory
  | Port
  | DestinationA
  | DestinationB
  deriving (Show, Eq)

-- means of transportation

data Transportation
  = Truck1
  | Truck2
  | Ship
  deriving Show

loadPlace :: Transportation -> Place
loadPlace Truck1 = Factory
loadPlace Truck2 = Factory
loadPlace Ship   = Port

-- topology

type Topology = Place -> Place -> Int

topology :: Topology
topology Factory      Factory      = 0
topology Factory      Port         = 1
topology Factory      DestinationB = 5
topology Port         Factory      = 1
topology Port         Port         = 0
topology Port         DestinationA = 4
topology DestinationA Port         = 4
topology DestinationA DestinationA = 0
topology DestinationB Factory      = 5
topology DestinationB DestinationB = 0

-- state

data Container = A | B
  deriving (Eq, Show)

containerDestination :: Transportation -> Container -> Place
containerDestination Truck1 A = Port
containerDestination Truck2 A = Port
containerDestination Truck1 B = DestinationB
containerDestination Truck2 B = DestinationB
containerDestination Ship   A = DestinationA

data ContainersDistribution = ContainersDistribution
  { _factory      :: Stock Container
  , _port         :: Stock Container
  , _destinationA :: Stock Container
  , _destinationB :: Stock Container
  }
  deriving Show

makeLenses ''ContainersDistribution

data Location = Location
  { place     :: Place
  , stockLens :: Lens' ContainersDistribution (Stock Container)
  }

updateContainerDistribution :: Place -> Stock Container -> ContainersDistribution -> ContainersDistribution
updateContainerDistribution Factory      = set factory
updateContainerDistribution Port         = set port
updateContainerDistribution DestinationA = set destinationA
updateContainerDistribution DestinationB = set destinationB

initialContainerDistribution :: [Container] -> ContainersDistribution
initialContainerDistribution factoryContainers = ContainersDistribution
  (Stock factoryContainers)
  emptyStock
  emptyStock
  emptyStock

-- | the first parameter denotes the destination
-- | the second parameter denotes the distance from the destination
-- | the third parameter denotes if the transportation is carrying a container
data TransportationLocation = TransportationLocation
  { _destination :: Place
  , _distance    :: Int
  , _cargo       :: (Maybe Container)
  }
  deriving Show

makeLenses ''TransportationLocation

data TransportationsState = TransportationsState
  { _truck1 :: TransportationLocation
  , _truck2 :: TransportationLocation
  , _ship   :: TransportationLocation
  }
  deriving Show

makeLenses ''TransportationsState

data Carrier = Carrier
  { transportation :: Transportation
  , locationLens   :: Lens' TransportationsState TransportationLocation
  }

initialTrasportationState :: TransportationsState
initialTrasportationState = TransportationsState
  (TransportationLocation Factory 0 Nothing)
  (TransportationLocation Factory 0 Nothing)
  (TransportationLocation Port    0 Nothing)

data Status = Status
  { _distribution    :: ContainersDistribution
  , _transportations :: TransportationsState
  }
  deriving Show

makeLenses ''Status

initialStatus :: [Container] -> Status
initialStatus factoryContainers = Status
  (initialContainerDistribution factoryContainers)
  initialTrasportationState

-- evolution

loadUnload :: (Location -> Carrier -> Status -> Status) -> Location -> Carrier -> State Status ()
loadUnload action location carrier = state (((),) . doLoadUnload action location carrier)
  where
    doLoadUnload :: (Location -> Carrier -> Status -> Status) -> Location -> Carrier -> Status -> Status
    doLoadUnload action (Location place stockLens) (Carrier transportation locationLens) status =
      case (view (transportations . locationLens . destination) status, view (transportations . locationLens . distance) status) of
        (aimPlace, 0) -> if (place == aimPlace)
                         then action location carrier status
                         else status
        _             -> status

---- load

loadContainer :: Container -> Location -> Carrier -> Status -> Status
loadContainer item (Location place stockLens) (Carrier transportation locationLens) =
  set (transportations . locationLens . destination) (containerDestination transportation item) .
  set (transportations . locationLens . distance) (topology place (containerDestination transportation item)) .
  set (transportations . locationLens . cargo) (Just item)

loadAction :: Location -> Carrier -> Status -> Status
loadAction location@(Location place stockLens) carrier status =
  let stock                 = view (distribution . stockLens) status
      (maybeItem, newStock) = getItemFromStock stock
      statusUpdatingStock   = set (distribution . stockLens) newStock status
  in case maybeItem of
        Nothing   -> statusUpdatingStock
        Just item -> loadContainer item location carrier statusUpdatingStock

load :: Location -> Carrier -> State Status ()
load = loadUnload loadAction

loadTruck1 :: State Status ()
loadTruck1 = load (Location Factory factory) (Carrier Truck1 truck1)

loadTruck2 :: State Status ()
loadTruck2 = load (Location Factory factory) (Carrier Truck2 truck2)

loadShip :: State Status ()
loadShip = load (Location Port port) (Carrier Ship ship)

---- unload

unloadContainer :: Location -> Carrier -> Status -> Status
unloadContainer (Location place stockLens) (Carrier transportation locationLens) =
  set (transportations . locationLens . destination) (loadPlace transportation) .
  set (transportations . locationLens . distance) (topology place (loadPlace transportation)) .
  set (transportations . locationLens . cargo) Nothing

unloadAction :: Location -> Carrier -> Status -> Status
unloadAction location@(Location place stockLens) carrier@(Carrier transportation locationLens) status =
  let carrierCargo = view (transportations . locationLens . cargo) status
  in case carrierCargo of
    Nothing   -> status
    Just item -> unloadContainer location carrier .
                 over (distribution . stockLens) (addItemToStock item) $
                 status

unload :: Location -> Carrier -> State Status ()
unload = loadUnload unloadAction

unloadTruck1AtPort :: State Status ()
unloadTruck1AtPort = unload (Location Port port) (Carrier Truck1 truck1)

unloadTruck2AtPort :: State Status ()
unloadTruck2AtPort = unload (Location Port port) (Carrier Truck2 truck2)

unloadTruck1AtDestinationB :: State Status ()
unloadTruck1AtDestinationB = unload (Location DestinationB destinationB) (Carrier Truck1 truck1)

unloadTruck2AtDestinationB :: State Status ()
unloadTruck2AtDestinationB = unload (Location DestinationB destinationB) (Carrier Truck2 truck2)

unloadShipAtDestinationA :: State Status ()
unloadShipAtDestinationA = unload (Location DestinationA destinationA) (Carrier Ship ship)

-- move

moveTransportation :: TransportationLocation -> TransportationLocation
moveTransportation = over distance (\i -> max 0 (i - 1))

moveTransportations :: TransportationsState -> TransportationsState
moveTransportations = over truck1 moveTransportation . over truck2 moveTransportation . over ship moveTransportation

move :: State Status ()
move = state (\status -> ((), over transportations moveTransportations status))

-- final state

noContainerIsInTheWrongStock :: ContainersDistribution -> Bool
noContainerIsInTheWrongStock distribution =  isEmpty (view factory distribution)
                                          && isEmpty (view port    distribution)
                                          && containsOnly A (view destinationA distribution)
                                          && containsOnly B (view destinationB distribution)

noTransportationCarriesAContainer :: TransportationsState -> Bool
noTransportationCarriesAContainer transportations =  isNothing (view (truck1 . cargo) transportations)
                                                  && isNothing (view (truck2 . cargo) transportations)
                                                  && isNothing (view (ship   . cargo) transportations)

finished :: Status -> Bool
finished status =  noContainerIsInTheWrongStock      (view distribution status)
                && noTransportationCarriesAContainer (view transportations status)

-- execute

step :: State Status ()
step = do
  unloadTruck1AtPort
  unloadTruck2AtPort
  unloadTruck1AtDestinationB
  unloadTruck2AtDestinationB
  unloadShipAtDestinationA
  loadTruck1
  loadTruck2
  loadShip
  move
  unloadTruck1AtPort
  unloadTruck2AtPort
  unloadTruck1AtDestinationB
  unloadTruck2AtDestinationB
  unloadShipAtDestinationA
  loadTruck1
  loadTruck2
  loadShip

stepCount :: State (Status, Int) ()
stepCount = state $ const () &&& (execState step *** (+ 1))

loop :: State (Status, Int) ()
loop = do
  (status, count) <- get
  if finished (trace (show (status, count)) status)
  then return ()
  else do
    stepCount
    loop

main :: IO ()
main = putStrLn $ show $ flip execState (initialStatus [A, A, B, A, B, B, A, B], 0) loop
