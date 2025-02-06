sudo su $USER
docker --debug build -t neqlips .
docker run -it neqlips /bin/bash

docker start $docker_id
docker exec -it $docker_id /bin/bash

docker cp ./run.sh $docker_id:/NeqLIPS/run.sh
docker cp $docker_id:/NeqLIPS/Results ./

docker rm $(docker ps -aq)