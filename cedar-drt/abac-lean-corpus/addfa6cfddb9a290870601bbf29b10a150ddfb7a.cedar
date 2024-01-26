forbid(
  principal is r::B::E1::B1::a in r::B::E1::B1::a::"",
  action in [r::B::E1::B1::Action::"action"],
  resource is r::B::E1::B1::a in r::B::E1::B1::a::""
) when {
  (true && (principal[""])) && principal
};
