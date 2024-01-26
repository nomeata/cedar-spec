permit(
  principal is a in a::"",
  action == Action::"action",
  resource in a::""
) when {
  ((true && ("" == "")) && ("" == "")) && (["", "", ""] == ["", "", ""])
};
