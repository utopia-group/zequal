FROM rust:1.90.0

RUN apt update
RUN apt install z3
RUN apt install python3
COPY ./ /zequal

WORKDIR /zequal/
RUN cargo build
CMD [ "python3", "zequal.py", "./to_analyze/main*.circom" ]