ENV ?= rococo

list-env:
	@echo "syntax is:"
	@echo "          make start ENV=rococo"
	@echo ""
	@echo "available envs:"
	@ls -c1 env

start-para:
	docker-compose --env-file env/${ENV} -f parachain.yml up -d

start-para-persist:
	docker-compose --env-file env/${ENV} -f parachain.yml -f ./persistent_storage.yml up -d

start-relay:
	docker-compose --env-file env/${ENV} -f relaychain.yml up -d

stop:
	docker-compose -f parachain.yml down || true
	docker-compose -f relaychain.yml down || true

show-env:
	@echo "################################################################################"
	@echo "#                                  ENV                                         #"
	@echo "################################################################################"
	@cat env/${ENV}
	@echo "################################################################################"
	@echo

start: start-para start-relay

restart: stop start-para start-relay

reload: 
	docker-compose --env-file env/${ENV} -f parachain.yml restart para_alice para_bob

logs-para:
	docker-compose -f parachain.yml logs -f
	
logs-relay:
	docker-compose -f relaychain.yml logs -f

clean: stop
	sudo rm -rf ./data
