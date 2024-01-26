forbid(
  principal == a::"",
  action in [Action::"      "],
  resource == a::""
) when {
  (true && (Action::"      " in Action::"      ")) && (Action::"      " in Action::"      ")
};
