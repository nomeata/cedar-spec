@A("\0\0\0\0\0\0\0\0")
@r("")
permit(
  principal in a::"+j4",
  action == Action::"action",
  resource in a::"+j4"
) when {
  (true && (!"")) && a::"+j4"
};
