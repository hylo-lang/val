/// The type of metric to report
public enum MeasurementType: Int, CaseIterable {
  case Lexer = 0
  case Parser
  case TypeChecker
  case IRLowering
  case Depolymorphize
  case IRConversion
  case MandatoryPass
  case Optimizations
  case EmitPhase
  case LinkPhase

  public static var count: Int {
    return MeasurementType.allCases.count
  }
}

/// Time measurement probe. Will report time between init() and stop()
/// to the associate ProfilingMeasurements object
public struct TimeMeasurementProbe: ~Copyable {

  var beginning: ContinuousClock.Instant
  var measure_type: MeasurementType
  var pool: ProfilingMeasurements

  init(_ measure_type: MeasurementType, _ pool: ProfilingMeasurements) {
    self.beginning = ContinuousClock.Instant.now
    self.pool = pool
    self.measure_type = measure_type
  }

  public func stop() {
    let time: Duration = ContinuousClock.Instant.now - beginning
    pool.addProfiledDuration(self.measure_type, time)
  }

}

/// A container for profiling measurements
public class ProfilingMeasurements {

  public init() {}

  var cumulatedDurations: [Duration] = [Duration](
    repeating: Duration.seconds(0), count: MeasurementType.count)

  /// Create a new TimeMeasurementProbe for a given measure type
  public func createAndStartProfilingProbe(_ measure_type: MeasurementType) -> TimeMeasurementProbe
  {
    return TimeMeasurementProbe(measure_type, self)
  }

  /// Internal. Reserved for TimeMeasurementProbe
  internal func addProfiledDuration(_ measure_type: MeasurementType, _ duration: Duration) {
    self.cumulatedDurations[measure_type.rawValue] += duration
  }

  /// Print the current profiling report
  public func printProfilingReport() {
    let profilingReport = """
      **Compile time profiling summary**
        Frontend:
          Lexer: \(formattedMeasurement(MeasurementType.Lexer))
          Parser: \(formattedMeasurement(MeasurementType.Parser))
          TypeChecker: \(formattedMeasurement(MeasurementType.TypeChecker))
        Backend:
          IR Lowering: \(formattedMeasurement(MeasurementType.IRLowering))
          Depolymorphize: \(formattedMeasurement(MeasurementType.Depolymorphize))
          LLVM IR Conversion: \(formattedMeasurement(MeasurementType.IRConversion))                   
          LLVM Mandatory pass: \(formattedMeasurement(MeasurementType.MandatoryPass))                
          LLVM Optimizations: \(formattedMeasurement(MeasurementType.Optimizations))
          LLVM Emit phase: \(formattedMeasurement(MeasurementType.EmitPhase))
          Linking phase: \(formattedMeasurement(MeasurementType.LinkPhase))

      """
    print(profilingReport)
  }

  public func durationFor(_ measure_type: MeasurementType) -> Duration {
    switch measure_type {
    case .Parser:
      return cumulatedDurations[MeasurementType.Parser.rawValue]
        - cumulatedDurations[MeasurementType.Lexer.rawValue]
    default:
      return cumulatedDurations[measure_type.rawValue]
    }
  }

  public func formattedMeasurement(_ measure_type: MeasurementType) -> String {
    let measure = durationFor(measure_type)
    let measureDouble =
      Double(measure.components.seconds) + Double(measure.components.attoseconds) / 1e18
    let unitArrays = ["s", "ms", "us", "ns", "ps"]
    var factor = 1
    for i in 0...unitArrays.count {
      let scaledMeasurement = measureDouble * Double(factor)
      if scaledMeasurement > 1.0 {
        return "\(String(format: "%.03f", scaledMeasurement)) \(unitArrays[i])"
      }
      factor *= 1000
    }
    return "N/A"
  }
}
